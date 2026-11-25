module

public import RKCert.ReviewedNative.WeakFiveSoleInnerIntegerCornerData
public import RKCert.ReviewedNative.FiniteGaussianGridPositivity
public import Mathlib.Algebra.Polynomial.OfFn

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Ring.Cast
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Native orthogonality and signs at the literal SoleInner density corners

The checked integer vector is normalized and identified with the monic
orthogonal sextic for the *published normalized density* at its original
corner. Positivity/uniqueness use the reviewed unit integration grid only.
This supplies the signed rational cages, not root ordering in a common
extension, node comparison, multiaffine caps or a SoleInner exclusion. -/
namespace RKCert.ReviewedNative.WeakFiveSoleInnerUniform

open Polynomial RKCert.Endpoint
open RKCert.ReviewedNative.PositiveRule19
open RKCert.ReviewedNative.FiniteGaussianGridPositivity
open scoped BigOperators Classical

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Compactification of the exterior ratio in the published continuous argument. -/
def normalizedRight (s c : K) : K := c*s/(1-s+c*s)

def affineWeight (s : K) : K[X] := C s + C (1-s)*X

/-- The exact density in the uniform argument, not a merely equivalent
collection of rounded or unnormalized data. -/
def density (s r : K) : K[X] := unitWeight K * affineWeight s * affineWeight r

def SixOrthogonal (s r : K) (P : K[X]) : Prop :=
  ∀ H : K[X], H.natDegree ≤ 5 → integral 0 1 (density s r * P * H) = 0

namespace CornerRow

variable (d : CornerRow) (K)

def s : K := (d.breakpoint : K)/64
def ratio : K := (d.ratioNum : K)/(d.ratioDen : K)
def r : K := normalizedRight (d.s K) (d.ratio K)

def lowerEndpoint (j : Fin 6) : K := (d.lower j : K)/4096
def upperEndpoint (j : Fin 6) : K := ((d.lower j+1 : ℕ) : K)/4096

def integerPolynomial : K[X] := ofFn 7 (fun j => (d.coefficient j : K))

/-- Divide the literal vector by its leading coefficient, not by a separately
solved monic vector. -/
def monicPolynomial : K[X] := d.integerPolynomial K * C ((d.coefficient 6 : K)⁻¹)

variable {K}

private theorem ratioNum_pos : 0 < d.ratioNum := by
  cases h : d.upper <;> simp [ratioNum,h]

private theorem ratioDen_pos : 0 < d.ratioDen := by
  cases h : d.upper <;> simp [ratioDen,h]

private theorem rightDen_pos : 0 < d.rightDen := by
  unfold rightDen
  by_cases h : d.breakpoint = 0
  · have hr : 0 < d.remaining := by simp [remaining,h]
    have ht := Nat.mul_pos d.ratioDen_pos hr
    omega
  · exact Nat.add_pos_left (Nat.mul_pos d.ratioNum_pos (Nat.pos_of_ne_zero h)) _

private theorem rightDen_pos_cast : (0 : K) < (d.rightDen : K) :=
  Nat.cast_pos.mpr d.rightDen_pos

private theorem sub_s_eq (hd : d.Verified) : 1-d.s K = (d.remaining : K)/64 := by
  have h : d.breakpoint+d.remaining=64 := Nat.add_sub_of_le hd.breakpoint_le
  have hK : (d.breakpoint : K)+(d.remaining : K)=64 := by exact_mod_cast h
  unfold s
  linarith only [hK]

private theorem normalized_den (hd : d.Verified) :
    1-d.s K+d.ratio K*d.s K = (d.rightDen : K)/((d.ratioDen : K)*64) := by
  have hv : (d.ratioDen : K) ≠ 0 := (Nat.cast_pos.mpr d.ratioDen_pos).ne'
  rw [d.sub_s_eq hd]
  simp only [ratio,s,rightDen,Nat.cast_add,Nat.cast_mul]
  field_simp [hv] <;> ring

private theorem r_eq (hd : d.Verified) :
    d.r K = ((d.ratioNum : K)*(d.breakpoint : K))/(d.rightDen : K) := by
  have hv : (d.ratioDen : K) ≠ 0 := (Nat.cast_pos.mpr d.ratioDen_pos).ne'
  have hD : (d.rightDen : K) ≠ 0 := (d.rightDen_pos_cast (K := K)).ne'
  rw [r,normalizedRight,d.normalized_den hd]
  unfold ratio s
  field_simp [hv,hD] <;> ring

private theorem sub_r_eq (hd : d.Verified) :
    1-d.r K = ((d.ratioDen : K)*(d.remaining : K))/(d.rightDen : K) := by
  have hD : (d.rightDen : K) ≠ 0 := (d.rightDen_pos_cast (K := K)).ne'
  rw [d.r_eq hd]
  field_simp [hD] <;> simp only [rightDen,Nat.cast_add,Nat.cast_mul] <;> ring

theorem coordinates_unit (hd : d.Verified) :
    (0 ≤ d.s K ∧ d.s K ≤ 1) ∧ (0 ≤ d.r K ∧ d.r K ≤ 1) := by
  have ha : 0 ≤ (d.breakpoint : K) := Nat.cast_nonneg _
  have hb : 0 ≤ (d.remaining : K) := Nat.cast_nonneg _
  have S0 : 0 ≤ d.s K := div_nonneg ha (by norm_num)
  have S1 : 0 ≤ 1-d.s K := by
    rw [d.sub_s_eq hd]
    exact div_nonneg hb (by norm_num)
  have R0 : 0 ≤ d.r K := by
    rw [d.r_eq hd]
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) ha) (d.rightDen_pos_cast (K := K)).le
  have R1 : 0 ≤ 1-d.r K := by
    rw [d.sub_r_eq hd]
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hb) (d.rightDen_pos_cast (K := K)).le
  exact ⟨⟨S0,sub_nonneg.mp S1⟩,⟨R0,sub_nonneg.mp R1⟩⟩

private theorem affine_s_scale (hd : d.Verified) :
    C (64 : K)*affineWeight (d.s K) = C (d.breakpoint : K)+C (d.remaining : K)*X := by
  have h0 : (64 : K)*d.s K = (d.breakpoint : K) := by
    unfold s
    field_simp <;> ring
  have h1 : (64 : K)*(1-d.s K) = (d.remaining : K) := by
    rw [d.sub_s_eq hd]
    field_simp <;> ring
  simp only [affineWeight,mul_add,←mul_assoc,←map_mul,h0,h1]

private theorem affine_r_scale (hd : d.Verified) :
    C (d.rightDen : K)*affineWeight (d.r K) =
      C ((d.ratioNum : K)*(d.breakpoint : K)) +
        C ((d.ratioDen : K)*(d.remaining : K))*X := by
  have hD : (d.rightDen : K) ≠ 0 := (d.rightDen_pos_cast (K := K)).ne'
  have h0 : (d.rightDen : K)*d.r K=(d.ratioNum : K)*(d.breakpoint : K) := by
    rw [d.r_eq hd]
    field_simp [hD] <;> ring
  have h1 : (d.rightDen : K)*(1-d.r K)=(d.ratioDen : K)*(d.remaining : K) := by
    rw [d.sub_r_eq hd]
    field_simp [hD] <;> ring
  simp only [affineWeight,mul_add,←mul_assoc,←map_mul,h0,h1]

private theorem density_scale (hd : d.Verified) :
    C ((64 : K)*(d.rightDen : K))*density (d.s K) (d.r K) =
      unitWeight K * (C (d.weight0 : K)+C (d.weight1 : K)*X+C (d.weight2 : K)*X^2) := by
  calc
    _ = unitWeight K * ((C (64 : K)*affineWeight (d.s K)) *
        (C (d.rightDen : K)*affineWeight (d.r K))) := by
      simp only [density,map_mul]
      ring
    _ = _ := by
      rw [d.affine_s_scale hd,d.affine_r_scale hd]
      simp only [weight0,weight1,weight2,Nat.cast_mul,Nat.cast_add,Nat.cast_pow,
        map_mul,map_add,map_pow]
      ring

private theorem unit_power (n : ℕ) :
    integral (0 : K) 1 (X^n) = 1/((n+1 : ℕ) : K) := by
  rw [←monomial_one_right_eq_X_pow,integral_zero_left]
  simp [formalPrimitive,support_monomial n (one_ne_zero : (1 : K) ≠ 0)]

private def bubblePower (n : ℕ) : K := 1/(((n+2 : ℕ) : K)*((n+3 : ℕ) : K))

private theorem bubble_power (n : ℕ) :
    integral (0 : K) 1 (unitWeight K * X^n) = bubblePower (K := K) n := by
  have e : unitWeight K * X^n = X^(n+1)-X^(n+2) := by
    simp only [unitWeight,pow_add,pow_one,pow_two]
    ring
  rw [e,map_sub,unit_power,unit_power,show n+1+1=n+2 by omega,show n+2+1=n+3 by omega]
  have hp : (((n+2 : ℕ) : K)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hq : (((n+3 : ℕ) : K)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  unfold bubblePower
  field_simp [hp,hq] <;> simp only [Nat.cast_add,Nat.cast_ofNat] <;> ring

private theorem bubbleQuot_cast {n : ℕ} (hn : n < 14) :
    (bubbleQuot n : K) = (720720 : K)*bubblePower (K := K) n := by
  have hp : (((n+2 : ℕ) : K)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hq : (((n+3 : ℕ) : K)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have e := congrArg (fun x : ℕ => (x : K)) (bubbleQuot_exact ⟨n,hn⟩)
  have e' : (bubbleQuot n : K)*(((n+2 : ℕ) : K)*((n+3 : ℕ) : K)) = 720720 := by
    simpa only [bubbleDen,Nat.cast_mul,Nat.cast_ofNat] using e
  rw [bubblePower,mul_one_div]
  exact (eq_div_iff (mul_ne_zero hp hq)).mpr e'

private theorem clearedMoment_cast (hd : d.Verified) {n : ℕ} (hn : n ≤ 11) :
    (d.clearedMoment n : K) =
      ((720720 : K)*(64*(d.rightDen : K)))*
        integral 0 1 (density (d.s K) (d.r K)*X^n) := by
  let S : K := 64*(d.rightDen : K)
  have e : C S * (density (d.s K) (d.r K)*X^n) =
      C (d.weight0 : K)*(unitWeight K*X^n) +
      C (d.weight1 : K)*(unitWeight K*X^(n+1)) +
      C (d.weight2 : K)*(unitWeight K*X^(n+2)) := by
    rw [←mul_assoc,d.density_scale hd]
    simp only [pow_add,pow_one,pow_two]
    ring
  have e' := congrArg (fun P : K[X] => integral (0 : K) 1 P) e
  change integral 0 1 (C S * (density (d.s K) (d.r K)*X^n)) = _ at e'
  simp only [map_add,←Polynomial.smul_eq_C_mul,map_smul,smul_eq_mul,bubble_power] at e'
  change (d.clearedMoment n : K) =
    ((720720 : K)*S)*integral 0 1 (density (d.s K) (d.r K)*X^n)
  simp only [clearedMoment,Nat.cast_add,Nat.cast_mul,bubbleQuot_cast (K := K) (show n < 14 by omega),
    bubbleQuot_cast (K := K) (show n+1 < 14 by omega),
    bubbleQuot_cast (K := K) (show n+2 < 14 by omega)]
  rw [mul_assoc, e']
  ring

private theorem coefficient_top : (d.integerPolynomial K).coeff 6 = (d.coefficient 6 : K) := by
  rw [integerPolynomial,ofFn_coeff_eq_val_of_lt _ (show 6 < 7 by decide)] <;> rfl

private theorem coefficient_pos (hd : d.Verified) : (0 : K) < (d.coefficient 6 : K) :=
  Int.cast_pos.mpr hd.positive_top

private theorem integer_degree (hd : d.Verified) : (d.integerPolynomial K).natDegree=6 := by
  have hlt : (d.integerPolynomial K).natDegree < 7 :=
    ofFn_natDegree_lt (by decide) _
  apply natDegree_eq_of_le_of_coeff_ne_zero (by omega)
  rw [d.coefficient_top]
  exact (d.coefficient_pos hd).ne'

private theorem integer_power_zero (hd : d.Verified) (i : Fin 6) :
    integral 0 1 (density (d.s K) (d.r K)*d.integerPolynomial K*X^i.val)=0 := by
  have scaleNe : ((720720 : K)*(64*(d.rightDen : K))) ≠ 0 :=
    mul_ne_zero (by norm_num) (mul_ne_zero (by norm_num) (d.rightDen_pos_cast (K := K)).ne')
  apply (mul_eq_zero.mp ?_).resolve_left scaleNe
  rw [integerPolynomial,ofFn_eq_sum_monomial,Finset.mul_sum,Finset.sum_mul,map_sum,Finset.mul_sum]
  have h := congrArg (fun z : ℤ => (z : K)) (hd.dot_zero i)
  change ((d.clearedDot i : ℤ) : K) = ((0 : ℤ) : K) at h
  simp only [clearedDot,Int.cast_sum,Int.cast_mul,Int.cast_natCast,Int.cast_zero] at h
  refine Eq.trans ?_ h
  apply Finset.sum_congr rfl
  intro j _
  have hn : i.val+j.val≤11 := by have := i.isLt; have := j.isLt; omega
  rw [d.clearedMoment_cast hd hn]
  have e : density (d.s K) (d.r K)*monomial j.val (d.coefficient j : K)*X^i.val =
      C (d.coefficient j : K)*(density (d.s K) (d.r K)*X^(i.val+j.val)) := by
    simp only [←C_mul_X_pow_eq_monomial,pow_add]
    ring
  rw [e,←Polynomial.smul_eq_C_mul,map_smul,smul_eq_mul]
  ring

private theorem integer_orthogonal (hd : d.Verified) :
    SixOrthogonal (d.s K) (d.r K) (d.integerPolynomial K) := by
  intro H hH
  let L : K[X] →ₗ[K] K := (integral 0 1).comp
    (LinearMap.mulLeft K (density (d.s K) (d.r K)*d.integerPolynomial K))
  change L H = 0
  rw [H.as_sum_range' 6 (by omega),map_sum]
  apply Finset.sum_eq_zero
  intro j hj
  have z : L (X^j) = 0 := d.integer_power_zero hd ⟨j,Finset.mem_range.mp hj⟩
  rw [←C_mul_X_pow_eq_monomial,←Polynomial.smul_eq_C_mul,map_smul,z,smul_zero]

theorem monicPolynomial_monic (hd : d.Verified) : (d.monicPolynomial K).Monic := by
  have n : d.integerPolynomial K ≠ 0 := by
    intro z
    have h := d.coefficient_top (K := K)
    rw [z,coeff_zero] at h
    exact (d.coefficient_pos (K := K) hd).ne' h.symm
  have lead : (d.integerPolynomial K).leadingCoeff = (d.coefficient 6 : K) := by
    rw [leadingCoeff,d.integer_degree hd,d.coefficient_top]
  rw [monicPolynomial,←lead]
  exact monic_mul_leadingCoeff_inv n

theorem monicPolynomial_degree (hd : d.Verified) : (d.monicPolynomial K).natDegree=6 := by
  rw [monicPolynomial,natDegree_mul_C (inv_ne_zero (d.coefficient_pos (K := K) hd).ne'),
    d.integer_degree hd]

theorem monicPolynomial_orthogonal (hd : d.Verified) :
    SixOrthogonal (d.s K) (d.r K) (d.monicPolynomial K) := by
  intro H hH
  have e : density (d.s K) (d.r K)*d.monicPolynomial K*H =
      C ((d.coefficient 6 : K)⁻¹)*(density (d.s K) (d.r K)*d.integerPolynomial K*H) := by
    unfold monicPolynomial
    ring
  rw [e,←Polynomial.smul_eq_C_mul,map_smul,d.integer_orthogonal hd H hH,smul_zero]

private theorem clearedValue_cast (m : ℕ) :
    (d.clearedValue m : K) = (4096 : K)^6*(d.integerPolynomial K).eval ((m : K)/4096) := by
  rw [clearedValue,Int.cast_sum,integerPolynomial,ofFn_eq_sum_monomial,
    eval_finsetSum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [eval_monomial,Int.cast_mul,Int.cast_pow,Int.cast_natCast,Int.cast_ofNat]
  have h : j.val+(6-j.val)=6 := by have := j.isLt; omega
  have p : (4096 : K)^6 = (4096 : K)^j.val*(4096 : K)^(6-j.val) := by
    rw [←pow_add,h]
  rw [p,div_pow]
  field_simp [pow_ne_zero j.val (by norm_num : (4096 : K) ≠ 0)] <;> ring

theorem monicPolynomial_cage_sign (hd : d.Verified) (j : Fin 6) :
    (d.monicPolynomial K).eval (d.lowerEndpoint K j) *
      (d.monicPolynomial K).eval (d.upperEndpoint K j) < 0 := by
  have h : (((d.clearedValue (d.lower j)*d.clearedValue (d.lower j+1)) : ℤ) : K) < 0 :=
    Int.cast_lt_zero.mpr (hd.endpoint_signs j)
  change _ < (0 : K) at h
  simp only [Int.cast_mul,d.clearedValue_cast] at h
  let p := (d.integerPolynomial K).eval (d.lowerEndpoint K j)
  let q := (d.integerPolynomial K).eval (d.upperEndpoint K j)
  change ((4096 : K)^6*p)*((4096 : K)^6*q)<0 at h
  have e : ((4096 : K)^6*p)*((4096 : K)^6*q) = ((4096 : K)^6)^2*(p*q) := by ring
  rw [e] at h
  have sign := neg_of_mul_neg_right h (sq_nonneg ((4096 : K)^6))
  let c : K := (d.coefficient 6 : K)⁻¹
  change (d.integerPolynomial K*C c).eval (d.lowerEndpoint K j) *
    (d.integerPolynomial K*C c).eval (d.upperEndpoint K j) < 0
  simp only [eval_mul,eval_C]
  change (p*c)*(q*c)<0
  have h' : (p*c)*(q*c) = (p*q)*c^2 := by ring
  rw [h']
  exact mul_neg_of_neg_of_pos sign (sq_pos_of_ne_zero
    (inv_ne_zero (d.coefficient_pos (K := K) hd).ne'))

end CornerRow

private theorem affine_degree (s : K) : (affineWeight s).natDegree ≤ 1 := by
  unfold affineWeight
  apply natDegree_add_le_of_degree_le
  · simp
  · exact natDegree_mul_le_of_le (m := 0) (n := 1) (by simp) natDegree_X.le

theorem density_degree (s r : K) : (density s r).natDegree ≤ 4 := by
  apply natDegree_mul_le_of_le (m := 3) (n := 1)
  · exact natDegree_mul_le_of_le unitWeight_degree (affine_degree s)
  · exact affine_degree r

private theorem affine_eval_pos {s x : K} (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1) (hx : 0 < x) :
    0 < (affineWeight s).eval x := by
  simp only [affineWeight,eval_add,eval_mul,eval_C,eval_X]
  by_cases hs : s=0
  · simpa only [hs,sub_zero,one_mul,zero_add] using hx
  · exact add_pos_of_pos_of_nonneg (lt_of_le_of_ne hs₀ (fun e => hs e.symm))
      (mul_nonneg (sub_nonneg.mpr hs₁) hx.le)

theorem density_eval_pos {s r x : K} (hs : s ∈ Set.Icc (0 : K) 1) (hr : r ∈ Set.Icc (0 : K) 1)
    (hx : x ∈ Set.Ioo (0 : K) 1) : 0 < (density s r).eval x := by
  simp only [density,eval_mul]
  exact mul_pos (mul_pos (unitWeight_eval_pos hx.1 hx.2) (affine_eval_pos hs.1 hs.2 hx.1))
    (affine_eval_pos hr.1 hr.2 hx.1)

/-- The paid degree-14 square makes the monic orthogonal sextic unique.
The argument applies to the entire compact parameter square. -/
theorem monic_unique {s r : K} (hs : s ∈ Set.Icc (0 : K) 1) (hr : r ∈ Set.Icc (0 : K) 1)
    {P Q : K[X]} (mp : P.Monic) (mq : Q.Monic) (dp : P.natDegree=6) (dq : Q.natDegree=6)
    (op : SixOrthogonal s r P) (oq : SixOrthogonal s r Q) : P=Q := by
  by_contra h
  let D := P-Q
  have hn : D ≠ 0 := sub_ne_zero.mpr h
  have heq : P.degree=Q.degree := by
    rw [degree_eq_natDegree mp.ne_zero,degree_eq_natDegree mq.ne_zero,dp,dq]
  have lp : P.leadingCoeff=1 := mp
  have lq : Q.leadingCoeff=1 := mq
  have hl : D.degree<P.degree := degree_sub_lt_left heq mp.ne_zero (lp.trans lq.symm)
  rw [degree_eq_natDegree mp.ne_zero,dp] at hl
  have dlt : D.natDegree<6 := (natDegree_lt_iff_degree_lt hn).mpr hl
  have dd : D.natDegree≤5 := by omega
  have eq : density s r * D^2 = density s r * P * D - density s r * Q * D := by
    unfold D
    ring
  have z : integral 0 1 (density s r * D^2)=0 := by
    rw [eq,map_sub,op D dd,oq D dd,sub_zero]
  have wn : density s r ≠ 0 := by
    intro ze
    have ev := density_eval_pos hs hr (show (1/2 : K) ∈ Set.Ioo (0 : K) 1 by
      exact ⟨by norm_num,by norm_num⟩)
    rw [ze,eval_zero] at ev
    exact (lt_irrefl _ ev)
  have dl : (density s r * D^2).natDegree≤14 :=
    natDegree_mul_le_of_le (density_degree s r) (natDegree_pow_le_of_le 2 dd)
  have good : 0 < integral 0 1 (density s r * D^2) := by
    apply integral_pos_of_grid_nonneg zero_lt_one _ (mul_ne_zero wn (pow_ne_zero 2 hn))
      (dl.trans_lt (by decide))
    intro i
    simp only [eval_mul,eval_pow]
    exact mul_nonneg (density_eval_pos hs hr (intervalPoint_mem zero_lt_one i)).le (sq_nonneg _)
  exact good.ne' z

/-- The six original signed disjoint unit cages, with strictly ordered
neighbors. A subsequent root-source consumer may read their signs. -/
structure SignedCages (d : CornerRow) (P : K[X]) : Prop where
  interior : ∀ j : Fin 6, 0 < d.lowerEndpoint K j ∧
    d.lowerEndpoint K j < d.upperEndpoint K j ∧ d.upperEndpoint K j < 1
  adjacent : ∀ j : Fin 5, d.upperEndpoint K j.castSucc < d.lowerEndpoint K j.succ
  signs : ∀ j : Fin 6, P.eval (d.lowerEndpoint K j) * P.eval (d.upperEndpoint K j) < 0

structure CornerWitness (d : CornerRow) (P : K[X]) : Prop where
  sUnit : d.s K ∈ Set.Icc (0 : K) 1
  rUnit : d.r K ∈ Set.Icc (0 : K) 1
  monic : P.Monic
  degree : P.natDegree=6
  orthogonal : SixOrthogonal (d.s K) (d.r K) P
  cages : SignedCages d P

theorem CornerRow.Verified.monic_witness {d : CornerRow} (hd : d.Verified) :
    CornerWitness d (d.monicPolynomial K) := by
  have hp := d.coordinates_unit (K := K) hd
  refine ⟨hp.1,hp.2,d.monicPolynomial_monic hd,d.monicPolynomial_degree hd,
    d.monicPolynomial_orthogonal hd,⟨?_,?_,d.monicPolynomial_cage_sign hd⟩⟩
  · intro j
    have den : (0 : K) < 4096 := by norm_num
    have lo : (0 : K) < (d.lower j : K) := Nat.cast_pos.mpr (hd.lower_pos j)
    have hi : ((d.lower j+1 : ℕ) : K) < (4096 : K) := by exact_mod_cast hd.upper_lt j
    have lt : (d.lower j : K) < ((d.lower j+1 : ℕ) : K) :=
      Nat.cast_lt.mpr (Nat.lt_succ_self _)
    refine ⟨div_pos lo den,div_lt_div_of_pos_right lt den,?_⟩
    exact (div_lt_iff₀ den).mpr (by simpa only [one_mul] using hi)
  · intro j
    apply div_lt_div_of_pos_right _ (by norm_num : (0 : K) < 4096)
    exact Nat.cast_lt.mpr (hd.separated j)

/-- A client's already-defined monic orthogonal corner polynomial inherits
the original cages by exact Gram uniqueness, with no linear solve. -/
theorem literal_cages_of_orthogonal {d : CornerRow} (hd : d.Verified) {P : K[X]}
    (mp : P.Monic) (dp : P.natDegree=6) (op : SixOrthogonal (d.s K) (d.r K) P) :
    SignedCages d P := by
  have W := hd.monic_witness (K := K)
  have e := monic_unique W.sUnit W.rUnit mp W.monic dp W.degree op W.orthogonal
  rw [e]
  exact W.cages

theorem literal_corner_witness (i : Fin 30) :
    CornerWitness (cornerRow i) ((cornerRow i).monicPolynomial K) :=
  (cornerRow_verified i).monic_witness

theorem lowCellCorner_coordinates (i : Fin 15) :
    (lowCellCorner i).s K = (cellBreaks i.castSucc : K)/64 ∧
      (lowCellCorner i).r K = normalizedRight ((cellBreaks i.castSucc : K)/64) (2/3) := by
  have label := lowCellCorner_label i
  have h : (lowCellCorner i).s K = (cellBreaks i.castSucc : K)/64 := by
    rw [CornerRow.s,label.1]
  exact ⟨h,by
    rw [CornerRow.r,h]
    simp [CornerRow.ratio,CornerRow.ratioNum,CornerRow.ratioDen,label.2]⟩

theorem highCellCorner_coordinates (i : Fin 15) :
    (highCellCorner i).s K = (cellBreaks i.succ : K)/64 ∧
      (highCellCorner i).r K = normalizedRight ((cellBreaks i.succ : K)/64) (6/7) := by
  have label := highCellCorner_label i
  have h : (highCellCorner i).s K = (cellBreaks i.succ : K)/64 := by
    rw [CornerRow.s,label.1]
  exact ⟨h,by
    rw [CornerRow.r,h]
    simp [CornerRow.ratio,CornerRow.ratioNum,CornerRow.ratioDen,label.2]⟩

/-- Every cell has both original signed orthogonal corner polynomials. -/
theorem cell_corner_witnesses (i : Fin 15) :
    CornerWitness (lowCellCorner i) ((lowCellCorner i).monicPolynomial K) ∧
      CornerWitness (highCellCorner i) ((highCellCorner i).monicPolynomial K) :=
  ⟨literal_corner_witness (lowRowIndex i),literal_corner_witness (highRowIndex i)⟩

/-- If a later producer already has either literal cell corner sextic,
its own polynomial has the checked cages by uniqueness. The caller
supplies exactly the published normalized density, not comparison data. -/
theorem lowCell_cages_of_orthogonal (i : Fin 15) {P : K[X]} (mp : P.Monic)
    (dp : P.natDegree=6)
    (op : SixOrthogonal ((cellBreaks i.castSucc : K)/64)
      (normalizedRight ((cellBreaks i.castSucc : K)/64) (2/3)) P) :
    SignedCages (lowCellCorner i) P := by
  obtain ⟨hs,hr⟩ := lowCellCorner_coordinates (K := K) i
  apply literal_cages_of_orthogonal (d := lowCellCorner i) (cornerRow_verified (lowRowIndex i)) mp dp
  rw [hs,hr]
  exact op

theorem highCell_cages_of_orthogonal (i : Fin 15) {P : K[X]} (mp : P.Monic)
    (dp : P.natDegree=6)
    (op : SixOrthogonal ((cellBreaks i.succ : K)/64)
      (normalizedRight ((cellBreaks i.succ : K)/64) (6/7)) P) :
    SignedCages (highCellCorner i) P := by
  obtain ⟨hs,hr⟩ := highCellCorner_coordinates (K := K) i
  apply literal_cages_of_orthogonal (d := highCellCorner i) (cornerRow_verified (highRowIndex i)) mp dp
  rw [hs,hr]
  exact op

end
end RKCert.ReviewedNative.WeakFiveSoleInnerUniform
