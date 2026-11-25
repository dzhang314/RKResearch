module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorMomentDefect
public import RKCert.ReviewedNative.WeakFiveThreeInteriorRayleighMin
public import Mathlib.Algebra.Polynomial.BigOperators

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Positive moment Gram forms on the full closed density interval

The finite positive rule gives strict quadratic positivity and monotonicity
in the density parameter. The field order is the supplied one; the proof
never assumes it is a sum-of-squares order.
-/
namespace RKCert.ReviewedNative.ThreeInteriorPencil

open Polynomial Matrix RKCert.ReviewedNative.PositiveRule19 RKCert.ReviewedNative.FiniteOrderedSigns
open RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
open scoped Polynomial Matrix BigOperators

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def vecPolynomial {n : ℕ} (v : Fin n → K) : K[X] := ∑ i, C (v i)*X^i.val

theorem vecPolynomial_coeff {n : ℕ} (v : Fin n → K) (i : Fin n) :
    (vecPolynomial v).coeff i.val = v i := by
  rw [vecPolynomial,finsetSum_coeff]
  rw [Finset.sum_eq_single i]
  · simp only [coeff_C_mul_X_pow, ite_true]
  · intro j _ hji
    have hij : i.val ≠ j.val := fun h => hji (Fin.ext h.symm)
    rw [coeff_C_mul_X_pow, if_neg hij]
  · intro hi
    exact (hi (Finset.mem_univ _)).elim

theorem vecPolynomial_degree {n d : ℕ} (v : Fin n → K) (fit : n ≤ d+1) :
    (vecPolynomial v).natDegree ≤ d := by
  unfold vecPolynomial
  apply natDegree_sum_le_of_forall_le
  intro i _
  apply (natDegree_C_mul_le _ _).trans
  rw [natDegree_X_pow]
  have h := i.isLt
  omega

theorem vecPolynomial_ne_zero {n : ℕ} {v : Fin n → K} (nonzero : v ≠ 0) :
    vecPolynomial v ≠ 0 := by
  intro z
  apply nonzero
  funext i
  rw [← vecPolynomial_coeff v i,z,coeff_zero] <;> rfl

def momentGram (n : ℕ) (J : K[X] →ₗ[K] K) (W : K[X]) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => J (W*X^(i.val+j.val))

theorem rayleigh_momentGram {n : ℕ} (J : K[X] →ₗ[K] K) (W : K[X]) (v : Fin n → K) :
    rayleigh (momentGram n J W) v = J (W*(vecPolynomial v)^2) := by
  have shape : W*(vecPolynomial v)^2 =
      ∑ j : Fin n, ∑ i : Fin n, C (v i*v j)*(W*X^(i.val+j.val)) := by
    rw [pow_two]
    unfold vecPolynomial
    rw [Finset.mul_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [C_mul,pow_add]
    ring
  rw [rayleigh,Matrix.dot_mulVec_eq_sum_sum,shape,map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← smul_eq_C_mul,map_smul,smul_eq_mul]
  change v i*J (W*X^(i.val+j.val))*v j = (v i*v j)*J (W*X^(i.val+j.val))
  ring

def gramB (n : ℕ) (s : K) : Matrix (Fin n) (Fin n) K :=
  momentGram n (threeInteriorScaledMoment s) 1

def gramA (n : ℕ) (s : K) : Matrix (Fin n) (Fin n) K :=
  momentGram n (threeInteriorScaledMoment s) X

def gramCap (n : ℕ) (s : K) : Matrix (Fin n) (Fin n) K :=
  momentGram n (threeInteriorScaledMoment s) (1-X)

theorem gramB_apply (n : ℕ) (s : K) (i j : Fin n) :
    gramB n s i j = threeInteriorScaledMoment s (X^(i.val+j.val)) := by
  simp only [gramB,momentGram,Matrix.of_apply,one_mul]

theorem gramA_apply (n : ℕ) (s : K) (i j : Fin n) :
    gramA n s i j = threeInteriorScaledMoment s (X^(i.val+j.val+1)) := by
  simp only [gramA,momentGram,Matrix.of_apply,pow_succ']

theorem gramCap_eq (n : ℕ) (s : K) : gramCap n s = gramB n s - gramA n s := by
  ext i j
  simp only [gramCap,gramB,gramA,momentGram,Matrix.of_apply,Matrix.sub_apply,sub_mul,one_mul,map_sub]

theorem leading_gramB (n : ℕ) (s : K) : leading (gramB (n+1) s) = gramB n s := rfl
theorem leading_gramA (n : ℕ) (s : K) : leading (gramA (n+1) s) = gramA n s := rfl
theorem leading_gramCap (n : ℕ) (s : K) : leading (gramCap (n+1) s) = gramCap n s := rfl

set_option maxHeartbeats 800000 in
theorem scaled_square_pos {s : K} (par : s ∈ Set.Icc 0 1) {W P : K[X]}
    (wd : W.natDegree ≤ 1) (pd : P.natDegree ≤ 6) (pn : P ≠ 0)
    (wp : ∀ x ∈ Set.Ioo (0:K) 1, 0 < W.eval x) :
    0 < threeInteriorScaledMoment s (W*P^2) := by
  change 0 < (12252240:K)*integral 0 1 (threeInteriorDensity s*(W*P^2))
  apply mul_pos (by norm_num)
  have d : (threeInteriorDensity s*(W*P^2)).natDegree ≤ 19 :=
    (natDegree_mul_le_of_le (threeInterior_density_degree s)
      (natDegree_mul_le_of_le wd (natDegree_pow_le_of_le 2 pd))).trans (by decide)
  have live (i : Fin 19) :
      0 < (threeInteriorDensity s).eval (intervalPoint (0:K) 1 i) *
        W.eval (intervalPoint (0:K) 1 i) :=
    mul_pos (threeInterior_density_pos par (intervalPoint_mem zero_lt_one i))
      (wp _ (intervalPoint_mem zero_lt_one i))
  apply integral_pos_of_grid_samples zero_lt_one d
  · intro i
    simp only [eval_mul,eval_pow,← mul_assoc]
    exact mul_nonneg (live i).le (sq_nonneg _)
  · obtain ⟨i,h⟩ := exists_nonzero_grid_sample (K := K) zero_lt_one pn (pd.trans_lt (by decide))
    refine ⟨i,?_⟩
    simp only [eval_mul,eval_pow,← mul_assoc]
    exact mul_pos (live i) (sq_pos_of_ne_zero h)

private theorem density_mono_eval {s t x : K} (st : s ≤ t) (hx : x ∈ Set.Icc 0 1) :
    (threeInteriorDensity s).eval x ≤ (threeInteriorDensity t).eval x := by
  have eq : (threeInteriorDensity t).eval x-(threeInteriorDensity s).eval x =
      (t-s)*x*(1-x)^2 := by
    simp only [threeInteriorDensity,threeInteriorResidual,eval_mul,eval_add,
      eval_sub,eval_one,eval_X,eval_C]
    ring
  rw [← sub_nonneg,eq]
  exact mul_nonneg (mul_nonneg (sub_nonneg.mpr st) hx.1) (sq_nonneg _)

set_option maxHeartbeats 800000 in
theorem scaled_square_mono {s t : K} (st : s ≤ t) {W P : K[X]}
    (wd : W.natDegree ≤ 1) (pd : P.natDegree ≤ 6)
    (wp : ∀ x ∈ Set.Ioo (0:K) 1, 0 ≤ W.eval x) :
    threeInteriorScaledMoment s (W*P^2) ≤ threeInteriorScaledMoment t (W*P^2) := by
  have dg (z : K) : (threeInteriorDensity z*(W*P^2)).natDegree ≤ 19 :=
    (natDegree_mul_le_of_le (threeInterior_density_degree z)
      (natDegree_mul_le_of_le wd (natDegree_pow_le_of_le 2 pd))).trans (by decide)
  change (12252240:K)*integral 0 1 (threeInteriorDensity s*(W*P^2)) ≤
    (12252240:K)*integral 0 1 (threeInteriorDensity t*(W*P^2))
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  rw [interval_exact 0 1 _ (dg s),interval_exact 0 1 _ (dg t)]
  apply Finset.sum_le_sum
  intro i _
  simp only [eval_mul,eval_pow]
  have inside := intervalPoint_mem (K := K) zero_lt_one i
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (density_mono_eval st ⟨inside.1.le,inside.2.le⟩)
      (mul_nonneg (wp _ inside) (sq_nonneg _)))
    (intervalWeight_pos (K := K) zero_lt_one i).le

local instance : StarRing K := starRingOfComm
local instance : TrivialStar K := ⟨fun _ => rfl⟩

theorem momentGram_posDef (n : ℕ) (fit : n ≤ 7) {s : K} (par : s ∈ Set.Icc 0 1)
    {W : K[X]} (wd : W.natDegree ≤ 1) (wp : ∀ x ∈ Set.Ioo (0:K) 1, 0 < W.eval x) :
    (momentGram n (threeInteriorScaledMoment s) W).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · apply Matrix.IsHermitian.ext
    intro i j
    simp only [star_trivial,momentGram,Matrix.of_apply]
    rw [Nat.add_comm]
  · intro v vn
    have h : 0 < rayleigh (momentGram n (threeInteriorScaledMoment s) W) v := by
      rw [rayleigh_momentGram]
      exact scaled_square_pos par wd (vecPolynomial_degree v fit) (vecPolynomial_ne_zero vn) wp
    simpa only [star_trivial,rayleigh] using h

def compactLower (s : K) : K := -rayleighCost (gramA 7 s)
def compactUpper (s : K) : K := rayleighCost (gramCap 7 s)

theorem x_unit_pos (x : K) (hx : x ∈ Set.Ioo (0:K) 1) : 0 < (X : K[X]).eval x := by
  simpa only [eval_X] using hx.1

theorem one_sub_x_unit_pos (x : K) (hx : x ∈ Set.Ioo (0:K) 1) :
    0 < (1-X : K[X]).eval x := by
  simpa only [eval_sub,eval_one,eval_X] using sub_pos.mpr hx.2

theorem every_rayleigh_min {s : K} (par : s ∈ Set.Icc 0 1) {W : K[X]}
    (wd : W.natDegree ≤ 1) (wp : ∀ x ∈ Set.Ioo (0:K) 1, 0 < W.eval x) :
    let M := momentGram 7 (threeInteriorScaledMoment s) W
    0 < rayleighCost M ∧ ∃ v : Fin 7 → K, v (Fin.last 6) = 1 ∧
      rayleigh M v = rayleighCost M ∧
      ∀ w : Fin 7 → K, w (Fin.last 6) = 1 → rayleighCost M ≤ rayleigh M w :=
  rayleigh_min_of_posDef (momentGram_posDef 7 le_rfl par wd wp)

theorem compact_bounds_sign {s : K} (par : s ∈ Set.Icc 0 1) :
    compactLower s < 0 ∧ 0 < compactUpper s :=
  ⟨neg_lt_zero.mpr (every_rayleigh_min par natDegree_X.le x_unit_pos).1,
   (every_rayleigh_min par (unit_right_weight_degree (K := K)).le one_sub_x_unit_pos).1⟩

theorem rayleighCost_density_mono {s t : K} (sp : s ∈ Set.Icc 0 1) (tp : t ∈ Set.Icc 0 1)
    (st : s ≤ t) {W : K[X]} (wd : W.natDegree ≤ 1)
    (wp : ∀ x ∈ Set.Ioo (0:K) 1, 0 < W.eval x) :
    rayleighCost (momentGram 7 (threeInteriorScaledMoment s) W) ≤
      rayleighCost (momentGram 7 (threeInteriorScaledMoment t) W) := by
  obtain ⟨_,v,vlast,atMin,_⟩ := every_rayleigh_min tp wd wp
  obtain ⟨_,_,_,_,lower⟩ := every_rayleigh_min sp wd wp
  rw [← atMin]
  apply (lower v vlast).trans
  rw [rayleigh_momentGram,rayleigh_momentGram]
  exact scaled_square_mono st wd (vecPolynomial_degree v le_rfl) (fun x hx => (wp x hx).le)

theorem compactLower_anti {s t : K} (sp : s ∈ Set.Icc 0 1) (tp : t ∈ Set.Icc 0 1) (st : s ≤ t) :
    compactLower t ≤ compactLower s :=
  neg_le_neg (rayleighCost_density_mono sp tp st natDegree_X.le x_unit_pos)

theorem compactUpper_mono {s t : K} (sp : s ∈ Set.Icc 0 1) (tp : t ∈ Set.Icc 0 1) (st : s ≤ t) :
    compactUpper s ≤ compactUpper t :=
  rayleighCost_density_mono sp tp st (unit_right_weight_degree (K := K)).le one_sub_x_unit_pos

end
end RKCert.ReviewedNative.ThreeInteriorPencil
