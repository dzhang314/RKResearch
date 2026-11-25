module

public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstNormalization
public import RKCert.ReviewedNative.PolynomialCertificateAffinePencil
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Checked rational corner signs for all weak-four first-stop shapes

One compact factor schema, one exact integral recurrence and the existing
separately-affine polynomial pencil wrapper. Neither the RK order predicate
nor its integral normalization is redefined.
-/
namespace RKCert.ReviewedNative.WeakFourFirstOnly

open Polynomial RKCert.Endpoint RKResearch.Certified.Graded
open RKCert.ReviewedNative.PositiveRule19
open RKCert.ReviewedNative.PolynomialCertificate
open scoped BigOperators

inductive CompactForm where
  | ordinary | lowFit | highFit
  deriving Inhabited, DecidableEq, Repr

section Field
variable {K : Type*} [Field K]

/-- Ascending pair: constant coefficient, then linear coefficient. -/
def CompactForm.coeff (f : CompactForm) (w : K) : K × K :=
  match f with
  | .ordinary => (-w,1-w)
  | .lowFit => (1-w,w)
  | .highFit => (1,-w)

noncomputable def CompactForm.base (f : CompactForm) : K[X] :=
  match f with
  | .ordinary => X
  | .lowFit => 1
  | .highFit => 1

noncomputable def CompactForm.slope (f : CompactForm) : K[X] :=
  match f with
  | .ordinary => -(X+1)
  | .lowFit => X-1
  | .highFit => -X

noncomputable def CompactForm.poly (f : CompactForm) (w : K) : K[X] :=
  C (f.coeff w).1 + C (f.coeff w).2*X

theorem CompactForm.poly_eq_pencil (f : CompactForm) (w : K) :
    f.poly w = f.base+C w*f.slope := by
  cases f <;> simp only [CompactForm.poly,CompactForm.coeff,CompactForm.base,
    CompactForm.slope,map_sub,map_neg,map_one] <;> ring

theorem compactOrdinary_poly (w : K) :
    CompactForm.ordinary.poly w = ordinaryFactor w := by
  simp only [CompactForm.poly,CompactForm.coeff,ordinaryFactor,map_neg,sub_eq_add_neg]
  exact add_comm _ _

theorem compactLowFit_poly (w : K) :
    CompactForm.lowFit.poly w = lowFitFactor w := by
  simp only [CompactForm.poly,CompactForm.coeff,lowFitFactor]
  exact add_comm _ _

theorem compactHighFit_poly (w : K) :
    CompactForm.highFit.poly w = highFitFactor w := by
  simp only [CompactForm.poly,CompactForm.coeff,highFitFactor,map_neg,map_one,neg_mul,
    sub_eq_add_neg]

/-- Rational (or field) evaluation of a unit integral against a product of
affine factors. This performs at most two recursive calls per factor. -/
def momentRec : List (K × K) → ℕ → K
  | [], k => 1/((k+1:ℕ):K)
  | (a,b)::r, k => a*momentRec r k + b*momentRec r (k+1)

theorem momentRec_map {L : Type*} [Field L] (e : K →+* L)
    (r : List (K × K)) (k : ℕ) :
    e (momentRec r k) =
      momentRec (r.map (fun z => (e z.1,e z.2))) k := by
  induction r generalizing k with
  | nil => simp only [momentRec,map_div₀,map_one,map_natCast,List.map_nil]
  | cons z r ih =>
    rcases z with ⟨a,b⟩
    simp only [momentRec,List.map_cons,map_add,map_mul,ih]

private theorem compactCoeff_map {L : Type*} [Field L] (e : K →+* L)
    (f : CompactForm) (x : K) :
    (e (f.coeff x).1,e (f.coeff x).2) = f.coeff (e x) := by
  cases f <;> simp only [CompactForm.coeff,map_neg,map_one,map_sub]

end Field

section Ordered
noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem integral_scaled (a : K) (P : K[X]) :
    integral 0 1 (C a*P) = a*integral 0 1 P := by
  simpa only [Polynomial.smul_eq_C_mul,smul_eq_mul] using
    (integral (0:K) 1).map_smul a P

theorem momentRec_eq_integral (r : List (K × K)) (k : ℕ) :
    momentRec r k =
      integral 0 1 (X^k*(r.map (fun z => C z.1+C z.2*X)).prod) := by
  induction r generalizing k with
  | nil =>
    simp only [momentRec,List.map_nil,List.prod_nil,mul_one,integral_zero_left,
      formalPrimitive_eq_native,X_pow_eq_monomial,primitive_monomial,eval_monomial,
      one_pow,Nat.cast_add,Nat.cast_one]
  | cons z r ih =>
    rcases z with ⟨a,b⟩
    let S := (r.map (fun z => C z.1+C z.2*X)).prod
    have eq : (X^k*((C a+C b*X)*S) : K[X]) =
        C a*(X^k*S)+C b*(X^(k+1)*S) := by rw [pow_succ]; ring
    change a*momentRec r k+b*momentRec r (k+1) =
      integral 0 1 (X^k*((C a+C b*X)*S))
    rw [eq,map_add,integral_scaled,integral_scaled,←ih,←ih]

theorem momentRec_eq_product {m : ℕ} (forms : Fin m → CompactForm)
    (x : Fin m → K) (k : ℕ) :
    momentRec (List.ofFn (fun i => (forms i).coeff (x i))) k =
      integral 0 1 (X^k*(∏ i,(forms i).poly (x i))) := by
  simp only [momentRec_eq_integral,List.map_ofFn,List.prod_ofFn,Function.comp_apply,CompactForm.poly]

end
end Ordered

/-- The schema matches an axis witness of the stored rational certificate.
The powers are 1 or 2 as selected by `second`. -/
structure AxisBox (m : ℕ) where
  forms : Fin m → CompactForm
  lower : Fin m → ℚ
  upper : Fin m → ℚ
  second : Bool
  positive : Bool

def AxisBox.power {m : ℕ} (B : AxisBox m) : ℕ := if B.second then 2 else 1

def AxisBox.rawAt {m : ℕ} (B : AxisBox m) (corners : Fin m → Bool) : ℚ :=
  let p := vertex B.lower B.upper corners
  momentRec (List.ofFn (fun i => (B.forms i).coeff (p i))) B.power

def AxisBox.check {m : ℕ} (B : AxisBox m) : Bool :=
  decide (∀ c : Fin m → Bool, if B.positive then 0<B.rawAt c else B.rawAt c<0)

section Ordered
noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem AxisBox.cast_rawAt {m : ℕ} (B : AxisBox m) (c : Fin m → Bool) :
    (B.rawAt c:K) = integral 0 1 (X^B.power *
      (∏ i,(B.forms i).poly
        (vertex (fun j => (B.lower j:K)) (fun j => (B.upper j:K)) c i))) := by
  let e := Rat.castHom K
  change e (B.rawAt c) = _
  rw [AxisBox.rawAt,momentRec_map,List.map_ofFn]
  simp only [Function.comp_def,compactCoeff_map]
  have p (i : Fin m) : e (vertex B.lower B.upper c i) =
      vertex (fun j => (B.lower j:K)) (fun j => (B.upper j:K)) c i := by
    cases h : c i <;> simp [vertex,h,e]
  simp only [p,momentRec_eq_product]

private theorem AxisBox.affine {m : ℕ} (B : AxisBox m) :
    SeparatelyAffine (fun x : Fin m → K =>
      integral 0 1 (X^B.power*(∏ i,(B.forms i).poly (x i)))) := by
  simp only [CompactForm.poly_eq_pencil]
  exact separatelyAffine_polynomial_pencil (integral (0:K) 1) (X^B.power)
    (fun i => (B.forms i).base) (fun i => (B.forms i).slope)

/-- A reflected rational box furnishes a contradiction to the two actual
unit moments in any ordered coefficient field (possibly the root extension). -/
theorem AxisBox.not_paid {m : ℕ} (B : AxisBox m) (ok : B.check=true)
    (x : Fin m → K)
    (inside : ∀ i, x i ∈ Set.Icc (B.lower i:K) (B.upper i:K)) :
    ¬ UnitPair (∏ i,(B.forms i).poly (x i)) := by
  let P : K[X] := ∏ i,(B.forms i).poly (x i)
  intro h
  have z : integral 0 1 (X^B.power*P)=0 := by
    cases hs : B.second
    · simpa only [AxisBox.power,hs,Bool.false_eq_true,if_false,pow_one] using h.1
    · simpa only [AxisBox.power,hs,if_true] using h.2
  have signs : ∀ c : Fin m → Bool, if B.positive then 0<B.rawAt c else B.rawAt c<0 :=
    of_decide_eq_true ok
  cases hp : B.positive
  · have v := box_of_vertices (B.affine (K:=K)) inside (mixClosed_strictUpper (0:K)) (by
      intro c
      rw [←B.cast_rawAt c]
      exact Rat.cast_lt_zero.mpr (by simpa [hp] using signs c))
    exact (ne_of_lt v) z
  · have v := box_of_vertices (B.affine (K:=K)) inside (mixClosed_strictLower (0:K)) (by
      intro c
      rw [←B.cast_rawAt c]
      exact Rat.cast_pos.mpr (by simpa [hp] using signs c))
    exact (ne_of_gt v) z

/-- Alignment of a finite fitting subset with an accepted normalized box.
The only shape-specific premises are the exact nonzero factor scales and
the real coefficient bounds. -/
theorem AxisBox.rejects_finite_fit {ι : Type*} {m : ℕ} (B : AxisBox m)
    (ok : B.check=true) (I : Finset ι) (r : ι → K) (a : K)
    (label : Fin m ≃ {i // i∈I}) (x scale : Fin m → K)
    (bound : ∀ i, x i ∈ Set.Icc (B.lower i:K) (B.upper i:K))
    (nonzero : ∀ i, scale i≠0)
    (form : ∀ i, C a*X-C (r (label i).val) = C (scale i)*(B.forms i).poly (x i)) :
    ¬ UnitPair (stoppedFactors r I a) := by
  have eq : stoppedFactors r I a = stoppedFactors (fun i => r (label i).val) Finset.univ a := by
    unfold stoppedFactors
    rw [←Finset.prod_coe_sort]
    exact (Fintype.prod_equiv label (fun i => C a*X-C (r (label i).val))
      (fun i => C a*X-C (r i.val)) (fun _ => rfl)).symm
  intro paid
  rw [eq] at paid
  apply B.not_paid ok x bound
  apply (unitPair_factors_iff (fun i => r (label i).val) Finset.univ a scale
    (fun i => (B.forms i).poly (x i)) (fun i _ => form i)
    (fun i _ => nonzero i)).mp
  exact paid

end
end Ordered
end RKCert.ReviewedNative.WeakFourFirstOnly
