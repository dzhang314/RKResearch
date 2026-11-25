module

public import RKCert.ReviewedNative.SDIRK118ScalarExistence

import RKCert.ReviewedNative.DyadicBox64
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace RKResearch.Certified.PaidDefectBridge.SDIRK118.AffineBoxReceipt

open RKCert.ReviewedNative.DyadicBox64
open ScalarExistence ClaimPin ScalarBindings Polynomial
open ScalarAffineResponse (seedCubic iota)
open scoped BigOperators

/-- Raw reciprocal endpoints, followed by one outward-rounded product.
The first enclosure supplies the numerator, the second a strictly
positive denominator interval. -/
private def positiveQuotient (A B : Box) : Option Box :=
  if 0 < B.lo then some (mul A ⟨B.hi⁻¹,B.lo⁻¹⟩) else none

private theorem quotient_encloses {A B D : Box} {u v : ℝ}
    (hu : encloses A u) (hv : encloses B v)
    (h : positiveQuotient A B = some D) : encloses D (u/v) := by
  by_cases hlo : 0 < B.lo
  · have e : mul A ⟨B.hi⁻¹,B.lo⁻¹⟩ = D := by
      simpa [positiveQuotient,hlo] using h
    have loR : 0 < (B.lo : ℝ) := by exact_mod_cast hlo
    have vp : 0 < v := loR.trans_le hv.1
    have hiR : 0 < (B.hi : ℝ) := vp.trans_le hv.2
    have invB : encloses ⟨B.hi⁻¹,B.lo⁻¹⟩ v⁻¹ := by
      simpa only [encloses,Rat.cast_inv] using
        And.intro ((inv_le_inv₀ hiR vp).2 hv.2) ((inv_le_inv₀ vp loR).2 hv.1)
    rw [← e, div_eq_mul_inv]
    exact mul_encloses hu invB
  · simp [positiveQuotient,hlo] at h

private inductive Expr where
  | input : Fin 3 → Expr
  | rat : ℚ → Expr
  | plus : Expr → Expr → Expr
  | minus : Expr → Expr → Expr
  | times : Expr → Expr → Expr
  | quo : Expr → Expr → Expr

private noncomputable def evalReal (x : Fin 3 → ℝ) : Expr → ℝ
  | .input i => x i
  | .rat q => (q : ℝ)
  | .plus a b => evalReal x a + evalReal x b
  | .minus a b => evalReal x a - evalReal x b
  | .times a b => evalReal x a * evalReal x b
  | .quo a b => evalReal x a / evalReal x b

private def combine (f : Box → Box → Option Box) : Option Box → Option Box → Option Box
  | some a,some b => f a b
  | _,_ => none

private def evalBox (x : Fin 3 → Box) : Expr → Option Box
  | .input i => some (x i)
  | .rat q => some (outward (point q))
  | .plus a b => combine (fun A B => some (add A B)) (evalBox x a) (evalBox x b)
  | .minus a b => combine (fun A B => some (sub A B)) (evalBox x a) (evalBox x b)
  | .times a b => combine (fun A B => some (mul A B)) (evalBox x a) (evalBox x b)
  | .quo a b => combine positiveQuotient (evalBox x a) (evalBox x b)

private theorem combine_sound {x y z : ℝ} {A B : Option Box} {D : Box}
    (f : Box → Box → Option Box)
    (ha : ∀ U, A = some U → encloses U x) (hb : ∀ V, B = some V → encloses V y)
    (hf : ∀ U V W, f U V = some W → encloses U x → encloses V y → encloses W z)
    (out : combine f A B = some D) : encloses D z := by
  cases A with
  | none => simp [combine] at out
  | some U =>
    cases B with
    | none => simp [combine] at out
    | some V =>
      exact hf U V D (by simpa only [combine] using out) (ha U rfl) (hb V rfl)

private theorem eval_sound (a : Fin 3 → Box) (x : Fin 3 → ℝ)
    (base : ∀ i, encloses (a i) (x i)) (e : Expr) :
    ∀ D, evalBox a e = some D → encloses D (evalReal x e) := by
  induction e with
  | input i =>
    intro D h
    have eq : a i = D := by simpa [evalBox] using h
    rw [← eq]
    exact base i
  | rat q =>
    intro D h
    have eq : outward (point q) = D := by simpa [evalBox] using h
    rw [← eq]
    exact outward_encloses (point_encloses q)
  | plus u v hu hv =>
    intro D h
    refine combine_sound (fun U V => some (add U V)) hu hv ?_ h
    intro U V W e hu' hv'
    rw [← Option.some.inj e]
    exact add_encloses hu' hv'
  | minus u v hu hv =>
    intro D h
    refine combine_sound (fun U V => some (sub U V)) hu hv ?_ h
    intro U V W e hu' hv'
    rw [← Option.some.inj e]
    exact sub_encloses hu' hv'
  | times u v hu hv =>
    intro D h
    refine combine_sound (fun U V => some (mul U V)) hu hv ?_ h
    intro U V W e hu' hv'
    rw [← Option.some.inj e]
    exact mul_encloses hu' hv'
  | quo u v hu hv =>
    intro D h
    exact combine_sound positiveQuotient hu hv
      (fun _ _ _ eq hu' hv' => quotient_encloses hu' hv' eq) h

local infixl:65 " +ₑ " => Expr.plus
local infixl:65 " -ₑ " => Expr.minus
local infixl:70 " *ₑ " => Expr.times
local infixl:70 " /ₑ " => Expr.quo
local notation "Kₑ" => Expr.rat

-- These fixed coefficient tables are the two root-products and the
-- convolution in the archived affine expression, in ascending degree.
private def jVec (s t : Expr) : Fin 4 → Expr :=
  let p0 := (Kₑ 0 -ₑ s) *ₑ (Kₑ 0 -ₑ t)
  let p1 := (Kₑ 0 -ₑ s) +ₑ (Kₑ 0 -ₑ t)
  let m := Kₑ 0 -ₑ Kₑ 1
  ![p0 *ₑ m,p0 +ₑ p1 *ₑ m,p1 +ₑ m,Kₑ 1]

private def diffVec (j : Fin 4 → Expr) : Fin 5 → Expr :=
  ![Kₑ 0 -ₑ j 0,j 0 /ₑ Kₑ 1 -ₑ j 1,j 1 /ₑ Kₑ 2 -ₑ j 2,
    j 2 /ₑ Kₑ 3 -ₑ j 3,j 3 /ₑ Kₑ 4 -ₑ Kₑ 0]

private def qVec (a c : Expr) : Fin 3 → Expr :=
  ![(Kₑ 0 -ₑ a) *ₑ (Kₑ 0 -ₑ c),(Kₑ 0 -ₑ a) +ₑ (Kₑ 0 -ₑ c),Kₑ 1]

private def convolution (p : Fin 3 → Expr) (q : Fin 5 → Expr) : Fin 7 → Expr :=
  ![p 0 *ₑ q 0,
    p 0 *ₑ q 1 +ₑ p 1 *ₑ q 0,
    p 0 *ₑ q 2 +ₑ p 1 *ₑ q 1 +ₑ p 2 *ₑ q 0,
    p 0 *ₑ q 3 +ₑ p 1 *ₑ q 2 +ₑ p 2 *ₑ q 1,
    p 0 *ₑ q 4 +ₑ p 1 *ₑ q 3 +ₑ p 2 *ₑ q 2,
    p 1 *ₑ q 4 +ₑ p 2 *ₑ q 3,
    p 2 *ₑ q 4]

private def powExpr (z : Expr) : ℕ → Expr
  | 0 => Kₑ 1
  | n+1 => powExpr z n *ₑ z

private def avgExpr (z : Expr) (u : Fin 7 → Expr) (j : ℕ) : Expr :=
  let b := fun k : Fin 7 =>
    (u k *ₑ powExpr z (k.val+j)) /ₑ Kₑ ((k.val+j+1 : ℕ) : ℚ)
  Kₑ 0 +ₑ b 0 +ₑ b 1 +ₑ b 2 +ₑ b 3 +ₑ b 4 +ₑ b 5 +ₑ b 6

private def aExpr (s : Expr) : Expr := (Kₑ 1 +ₑ s) *ₑ Kₑ (1/2)
private def zExpr (s : Expr) : Expr := aExpr s +ₑ s

private def ellExpr (s t c : Expr) (j : ℕ) : Expr :=
  avgExpr (zExpr s) (convolution (qVec (aExpr s) c) (diffVec (jVec s t))) j

private def responseCore (s c T ell0 ell1 : Expr) : Expr :=
  let a := aExpr s
  let z := zExpr s
  let r := s *ₑ Kₑ (1/3)
  let B := (Kₑ 1 -ₑ s) *ₑ (Kₑ 3 -ₑ s)
  let eta := (Kₑ 3 +ₑ s) /ₑ ((Kₑ 3 -ₑ s) *ₑ Kₑ 4)
  let L := (B -ₑ Kₑ 1) *ₑ (T -ₑ Kₑ 1) -ₑ eta *ₑ (T +ₑ Kₑ 1 -ₑ s *ₑ Kₑ 2)
  let M := eta *ₑ B -ₑ (B -ₑ Kₑ 1 -ₑ eta) *ₑ Kₑ 3
  let j := fun x => (x -ₑ z +ₑ c) *ₑ (ell0 *ₑ (z -ₑ x) -ₑ ell1)
  let i1 := j (Kₑ 1) /ₑ (Kₑ 1 -ₑ r)
  let ia := j a /ₑ (a -ₑ r)
  let ij := ((T -ₑ a) *ₑ i1 -ₑ (T -ₑ Kₑ 1) *ₑ ia) /ₑ (Kₑ 1 -ₑ a)
  (L *ₑ j r) /ₑ ((Kₑ 1 -ₑ r) *ₑ (a -ₑ r)) -ₑ (M *ₑ ij) *ₑ Kₑ (1/3)

private def responseExpr (s t c T : Expr) : Expr :=
  responseCore s c T (ellExpr s t c 0) (ellExpr s t c 1)

noncomputable section

open scoped Classical

private def stdBasis : MonomialBasis := Polynomial.basisMonomials ℝ

private theorem std : standardPowers stdBasis := by
  intro n
  change (Polynomial.monomial n (1 : ℝ)) = (X : ℝ[X])^n
  rw [Polynomial.monomial_one_right_eq_X_pow]

private theorem jVec_poly (x : Fin 3 → ℝ) (s t : Expr) :
    Jpoly (evalReal x s) (evalReal x t) = ofFn 4 (fun i => evalReal x (jVec s t i)) := by
  simp [Jpoly,cubic,linearFactor,jVec,evalReal,ofFn_eq_sum_monomial,
    Fin.sum_univ_succ,← C_mul_X_pow_eq_monomial,map_add,map_sub,map_mul] <;> ring

private theorem qVec_poly (x : Fin 3 → ℝ) (a c : Expr) :
    linearFactor (evalReal x a) * linearFactor (evalReal x c) =
      ofFn 3 (fun i => evalReal x (qVec a c i)) := by
  simp [linearFactor,qVec,evalReal,ofFn_eq_sum_monomial,Fin.sum_univ_succ,
    ← C_mul_X_pow_eq_monomial,map_add,map_sub,map_mul] <;> ring

private theorem convolution_poly (x : Fin 3 → ℝ) (p : Fin 3 → Expr) (q : Fin 5 → Expr) :
    ofFn 3 (fun i => evalReal x (p i)) * ofFn 5 (fun i => evalReal x (q i)) =
      ofFn 7 (fun i => evalReal x (convolution p q i)) := by
  simp [convolution,evalReal,ofFn_eq_sum_monomial,Fin.sum_univ_succ,
    ← C_mul_X_pow_eq_monomial,map_add,map_mul] <;> ring

private theorem diffVec_poly (x : Fin 3 → ℝ) (s t : Expr) :
    coefficientPrimitive stdBasis (Jpoly (evalReal x s) (evalReal x t)) -
        Jpoly (evalReal x s) (evalReal x t) =
      ofFn 5 (fun i => evalReal x (diffVec (jVec s t) i)) := by
  let P := Jpoly (evalReal x s) (evalReal x t)
  have pe : P = ofFn 4 (fun i => evalReal x (jVec s t i)) := jVec_poly x s t
  change coefficientPrimitive stdBasis P - P = _
  ext n
  rw [coeff_sub]
  cases n with
  | zero =>
    rw [primitive_coeff_zero_for_certificate stdBasis std, pe]
    simp [diffVec,evalReal,ofFn_coeff_eq_val_of_lt]
  | succ n =>
    rw [primitive_coeff_succ_for_certificate stdBasis std, pe]
    by_cases low : n < 4
    · have hn : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
      rcases hn with rfl | rfl | rfl | rfl <;>
        norm_num [diffVec,evalReal,ofFn_coeff_eq_val_of_lt,ofFn_coeff_eq_zero_of_ge]
    · rw [ofFn_coeff_eq_zero_of_ge _ (by omega),
        ofFn_coeff_eq_zero_of_ge _ (by omega),
        ofFn_coeff_eq_zero_of_ge _ (by omega)]
      simp

private theorem powExpr_eval (x : Fin 3 → ℝ) (z : Expr) (n : ℕ) :
    evalReal x (powExpr z n) = (evalReal x z)^n := by
  induction n with
  | zero => simp [powExpr,evalReal]
  | succ n ih => simp [powExpr,evalReal,ih,pow_succ]

private theorem avgExpr_eval (x : Fin 3 → ℝ) (z : Expr) (u : Fin 7 → Expr) (j : ℕ) :
    evalReal x (avgExpr z u j) =
      ∑ i : Fin 7, evalReal x (u i) *
        ((evalReal x z)^(i.val+j) / ((i.val+j+1 : ℕ) : ℝ)) := by
  simp [avgExpr,evalReal,powExpr_eval,Rat.cast_natCast,Fin.sum_univ_succ,mul_div_assoc] <;> ring

private theorem avg_ofFn (x : Fin 3 → ℝ) (z : Expr) (u : Fin 7 → Expr) (j : ℕ)
    (hz : evalReal x z ≠ 0) :
    avg stdBasis (evalReal x z)
        ((X : ℝ[X])^j * ofFn 7 (fun i => evalReal x (u i))) =
      evalReal x (avgExpr z u j) := by
  let Z := evalReal x z
  let U := ofFn 7 (fun i => evalReal x (u i))
  have uD : U.natDegree < 7 := ofFn_natDegree_lt (by decide) _
  have pay : ((X : ℝ[X])^j * U).natDegree < j+7 := by
    have e : ((X : ℝ[X])^j * U).natDegree ≤ j+U.natDegree :=
      natDegree_mul_le_of_le (natDegree_X_pow _).le le_rfl
    omega
  change avg stdBasis Z ((X : ℝ[X])^j * U) = _
  rw [avg_eq_coefficient_sum stdBasis std Z hz _ (j+7) pay, avgExpr_eval,
    Finset.sum_range_add]
  have early :
      (∑ k ∈ Finset.range j, ((X : ℝ[X])^j * U).coeff k * (Z^k / ((k+1:ℕ):ℝ))) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [coeff_X_pow_mul', if_neg (not_le_of_gt (Finset.mem_range.mp hk)),zero_mul]
  rw [early,zero_add,← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  have pick : ((X : ℝ[X])^j * U).coeff (j+i.val) = evalReal x (u i) := by
    rw [Nat.add_comm j,coeff_X_pow_mul]
    exact ofFn_coeff_eq_val_of_lt _ i.isLt
  rw [pick,Nat.add_comm j i.val]

private theorem a_eval (x : Fin 3 → ℝ) (s : Expr) :
    evalReal x (aExpr s) = aAt (evalReal x s) := by
  norm_num [aExpr,evalReal,aAt,Rat.cast_div] <;> ring

private theorem z_eval (x : Fin 3 → ℝ) (s : Expr) :
    evalReal x (zExpr s) = zAt (evalReal x s) := by
  simp [zExpr,evalReal,a_eval,zAt]

private theorem ell_eval (x : Fin 3 → ℝ) (s t c : Expr) (j : ℕ)
    (hz : zAt (evalReal x s) ≠ 0) :
    ellAvg stdBasis (evalReal x s) (evalReal x t) (evalReal x c) j =
      evalReal x (ellExpr s t c j) := by
  let A := linearFactor (aAt (evalReal x s))
  let C₀ := linearFactor (evalReal x c)
  let J := Jpoly (evalReal x s) (evalReal x t)
  let V := coefficientPrimitive stdBasis J - J
  have qa : A * C₀ = ofFn 3 (fun i => evalReal x (qVec (aExpr s) c i)) := by
    simpa only [a_eval] using qVec_poly x (aExpr s) c
  have qv : V = ofFn 5 (fun i => evalReal x (diffVec (jVec s t) i)) :=
    diffVec_poly x s t
  let u := convolution (qVec (aExpr s) c) (diffVec (jVec s t))
  have product : A * C₀ * V = ofFn 7 (fun i => evalReal x (u i)) := by
    rw [qa,qv]
    exact convolution_poly x _ _
  change avg stdBasis (zAt (evalReal x s)) ((X : ℝ[X])^j * A * C₀ * V) =
    evalReal x (avgExpr (zExpr s) u j)
  rw [show (X : ℝ[X])^j * A * C₀ * V = X^j * (A * C₀ * V) by simp only [mul_assoc],
    product, ← z_eval]
  exact avg_ofFn x (zExpr s) u j (by simpa only [z_eval] using hz)

private def scalarResponse (s c T l₀ l₁ : ℝ) : ℝ :=
  let r := s/3
  let a := aAt s
  let z := zAt s
  let e := etaBox s
  let j := fun u => (u-z+c) * (l₀*(z-u)-l₁)
  Ld s e T * j r / ((1-r)*(a-r)) -
    ((e*Bs s-3*(Bs s-1-e))/3) * iota r a j T

private theorem responseCore_eval (x : Fin 3 → ℝ) (s c T l₀ l₁ : Expr) :
    evalReal x (responseCore s c T l₀ l₁) =
      scalarResponse (evalReal x s) (evalReal x c) (evalReal x T)
        (evalReal x l₀) (evalReal x l₁) := by
  simp only [responseCore,scalarResponse,evalReal,a_eval,z_eval,Ld,Bs,etaBox,iota,
    Rat.cast_ofNat,Rat.cast_div,Rat.cast_one]
  rw [show (3-evalReal x s)*4 = 4*(3-evalReal x s) by ring]
  simp only [div_eq_mul_inv,one_mul,mul_assoc]
  ring

private theorem response_eq_affineBoxValue (x : Fin 3 → ℝ) (s t c T : Expr)
    (hz : zAt (evalReal x s) ≠ 0) :
    evalReal x (responseExpr s t c T) =
      affineBoxValue stdBasis (evalReal x s) (evalReal x t) (evalReal x c) (evalReal x T) := by
  rw [responseExpr,responseCore_eval,← ell_eval x s t c 0 hz,← ell_eval x s t c 1 hz] <;> rfl

private def realInputs (s t c : ℝ) : Fin 3 → ℝ := ![s,t,c]

private def inputBoxes : Fin 3 → Box :=
  ![⟨457148959716/(2:ℚ)^40,457148959717/(2:ℚ)^40⟩,
    ⟨138977439915/(2:ℚ)^40,138977439916/(2:ℚ)^40⟩,
    ⟨1270550/(2:ℚ)^20,1270551/(2:ℚ)^20⟩]

private theorem initial_encloses (s t c : ℝ)
    (hs : s ∈ Set.Icc sLo sHi) (ht : t ∈ Set.Icc tLo tHi)
    (hc : c ∈ Set.Icc cLo cHi) (i : Fin 3) :
    encloses (inputBoxes i) (realInputs s t c i) := by
  fin_cases i
  · simpa [inputBoxes,realInputs,encloses,sLo,sHi,Rat.cast_div,Rat.cast_pow] using hs
  · simpa [inputBoxes,realInputs,encloses,tLo,tHi,Rat.cast_div,Rat.cast_pow] using ht
  · simpa [inputBoxes,realInputs,encloses,cLo,cHi,Rat.cast_div,Rat.cast_pow] using hc

-- The only two output intervals from the archived affine receipt.
private def lowerReceipt : Box :=
  ⟨(-155803327669626 : ℚ)/scale,(-132079553156373 : ℚ)/scale⟩
private def upperReceipt : Box :=
  ⟨(105456769076090 : ℚ)/scale,(132743982375427 : ℚ)/scale⟩

private def atEnd (T : ℚ) : Expr :=
  responseExpr (.input 0) (.input 1) (.input 2) (Kₑ T)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1800000 in
private theorem lowerReceipt_exact : evalBox inputBoxes (atEnd (15/4)) = some lowerReceipt := by
  decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1800000 in
private theorem upperReceipt_exact : evalBox inputBoxes (atEnd 4) = some upperReceipt := by
  decide +kernel

/-- The literal affine field of the fixed-box BoxSignBindings, with
no quadratic/oldGuard hypothesis and no chosen root in the premise. -/
theorem affine_box_signs :
    ∀ s ∈ Set.Icc sLo sHi, ∀ t ∈ Set.Icc tLo tHi, ∀ c ∈ Set.Icc cLo cHi,
      affineBoxValue (Polynomial.basisMonomials ℝ) s t c (15/4) < 0 ∧
        0 < affineBoxValue (Polynomial.basisMonomials ℝ) s t c 4 := by
  intro s hs t ht c hc
  let x := realInputs s t c
  have bound := initial_encloses s t c hs ht hc
  have sp : 0 < s := (by norm_num [sLo] : 0 < sLo).trans_le hs.1
  have hz : zAt s ≠ 0 := by
    unfold zAt aAt
    exact (add_pos (div_pos (add_pos zero_lt_one sp) (by norm_num)) sp).ne'
  have hz' : zAt (evalReal x (.input 0)) ≠ 0 := by
    simpa [x,realInputs,evalReal] using hz
  have lo := sign_neg (eval_sound inputBoxes x bound _ _ lowerReceipt_exact)
    (by norm_num [lowerReceipt,scale] : lowerReceipt.hi < 0)
  have hi := sign_pos (eval_sound inputBoxes x bound _ _ upperReceipt_exact)
    (by norm_num [upperReceipt,scale] : 0 < upperReceipt.lo)
  unfold atEnd at lo hi
  rw [response_eq_affineBoxValue _ _ _ _ _ hz'] at lo hi
  constructor
  · simpa [stdBasis,x,realInputs,evalReal,Rat.cast_div] using lo
  · simpa [stdBasis,x,realInputs,evalReal] using hi

/-- At the selected cubic root the same two signs apply to the
unscaled native response; the existing eta identity does the conversion. -/
theorem affine_at_selected_bracket (s t c : ℝ)
    (hs : s ∈ Set.Icc sLo sHi) (ht : t ∈ Set.Icc tLo tHi)
    (hc : c ∈ Set.Icc cLo cHi) (seed : seedCubic s = 0) :
    affineAt (Polynomial.basisMonomials ℝ) s t c (15/4) < 0 ∧
      0 < affineAt (Polynomial.basisMonomials ℝ) s t c 4 := by
  have h3 : 3 - s ≠ 0 := (sub_pos.mpr (hs.2.trans_lt (by norm_num [sHi]))).ne'
  rw [affineAt_eq_boxValue _ s t c (15/4) seed h3,
    affineAt_eq_boxValue _ s t c 4 seed h3]
  exact affine_box_signs s hs t ht c hc

end
end RKResearch.Certified.PaidDefectBridge.SDIRK118.AffineBoxReceipt
