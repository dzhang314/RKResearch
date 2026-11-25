module

public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstPencil
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Exact rational references for the weak-four first-stop pencil

These are the seven moments of the degree-seven reference and the seven
moments of the degree-eight reference, not evaluations of any RK fibre.
All receipt proofs transport to arbitrary ordered fields.
-/
namespace RKCert.ReviewedNative.WeakFourFirstOnly

open Polynomial
open RKResearch.Certified.Graded
open scoped BigOperators

universe u
noncomputable section
variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

set_option maxRecDepth 6000
set_option maxHeartbeats 2000000

/-- The reference definitions use classical equality, while the ordered
field has its own instance. Polynomial coefficients do not depend on
this implementation choice. -/
private theorem ofFn_eq_of_decEq {L : Type*} [Field L] (d e : DecidableEq L)
    {n : ℕ} (v : Fin n → L) :
    @ofFn L _ d n v = @ofFn L _ e n v := by
  have de : d = e := by
    funext x y
    exact Subsingleton.elim (d x y) (e x y)
  cases de
  rfl

private theorem firstReferenceJ_ofFn :
    firstReferenceJ K = ofFn 8 ![-8,252,-2520,11550,-27720,36036,-24024,6435] := by
  unfold firstReferenceJ
  exact ofFn_eq_of_decEq _ _ _

private theorem firstReferenceK_ofFn :
    firstReferenceK K = ofFn 8 ![-36,840,-6930,27720,-60060,72072,-45045,11440] := by
  unfold firstReferenceK
  exact ofFn_eq_of_decEq _ _ _

private theorem firstReferenceL_ofFn :
    firstReferenceL K = ofFn 8 ![-8,280,-3080,15400,-40040,56056,-40040,11440] := by
  unfold firstReferenceL
  exact ofFn_eq_of_decEq _ _ _

/-- Explicit rational moments of a coefficient vector, using precisely the
reviewed native primitive. The two reference tests instantiate d=1,2. -/
theorem firstReference_ofFn_moment {n : ℕ} (v : Fin n → K) (i d : ℕ) :
    (primitive (X^i*(X^d*ofFn n v))).eval 1 =
      ∑ j : Fin n, v j/((i+j.val+d+1:ℕ):K) := by
  rw [←mul_assoc,←pow_add,ofFn_eq_sum_monomial,Finset.mul_sum,map_sum,eval_finsetSum]
  apply Finset.sum_congr rfl
  intro j _
  rw [X_pow_mul_monomial,primitive_monomial,eval_monomial,one_pow,mul_one]
  congr 2
  omega

private theorem coeff_ofFn7 (v : Fin 8 → K) :
    (ofFn 8 v).coeff 7 = v 7 :=
  ofFn_coeff_eq_val_of_lt v (by decide)

private theorem degree_ofFn8 {v : Fin 8 → K} (vn : v 7 ≠ 0) :
    (ofFn 8 v).natDegree=7 := by
  have h := ofFn_natDegree_lt (by decide : 1≤(8:ℕ)) v
  have d : 7≤(ofFn 8 v).natDegree :=
    le_natDegree_of_ne_zero (by simpa only [coeff_ofFn7] using vn)
  omega

theorem firstReferenceJ_degree : (firstReferenceJ K).natDegree=7 := by
  rw [firstReferenceJ_ofFn]
  apply degree_ofFn8
  norm_num

theorem firstReferenceK_degree : (firstReferenceK K).natDegree=7 := by
  rw [firstReferenceK_ofFn]
  apply degree_ofFn8
  norm_num

theorem firstReferenceK_leading : (firstReferenceK K).leadingCoeff=11440 := by
  rw [←coeff_natDegree,firstReferenceK_degree]
  norm_num [firstReferenceK_ofFn,coeff_ofFn7]

theorem firstReferenceJ_weighted : WeightedSix (firstReferenceJ K) := by
  intro i
  have momentValue := firstReference_ofFn_moment
    (![-8,252,-2520,11550,-27720,36036,-24024,6435] : Fin 8 → K) i.val 1
  simp only [pow_one] at momentValue
  rw [firstReferenceJ_ofFn,momentValue]
  fin_cases i <;> norm_num [Fin.sum_univ_succ]

theorem firstReferenceP₀_weighted : WeightedSix (firstReferenceP₀ K) := by
  intro i
  have h : (X:K[X])*(X*firstReferenceK K)=X^2*firstReferenceK K := by
    rw [pow_two,mul_assoc]
  unfold firstReferenceP₀
  rw [h,firstReferenceK_ofFn,firstReference_ofFn_moment]
  fin_cases i <;> norm_num [Fin.sum_univ_succ]

theorem firstReferenceP₁_identity :
    firstReferenceP₁ K=firstReferenceP₀ K-firstReferenceJ K := by
  letI : Infinite K := Infinite.of_injective (fun n : ℕ => (n : K)) Nat.cast_injective
  apply Polynomial.funext
  intro x
  simp only [firstReferenceP₀,firstReferenceP₁,firstReferenceJ_ofFn,firstReferenceK_ofFn,
    firstReferenceL_ofFn,ofFn_eq_sum_monomial,eval_finsetSum,eval_monomial,eval_mul,eval_sub,
    eval_X,eval_one]
  norm_num [Fin.sum_univ_succ] <;> ring

theorem firstReferenceJ_atZero : (firstReferenceJ K).eval 0 = -8 := by
  rw [←coeff_zero_eq_eval_zero]
  norm_num [firstReferenceJ_ofFn,ofFn_coeff_eq_val_of_lt]

theorem firstReferenceJ_atOne : (firstReferenceJ K).eval 1 = 1 := by
  rw [firstReferenceJ_ofFn,ofFn_eq_sum_monomial,eval_finsetSum]
  simp only [eval_monomial,one_pow,mul_one]
  norm_num [Fin.sum_univ_succ]

/-- The literal two-reference hypotheses of the structural reduction. -/
theorem firstPencilReferences_of_exact_moments :
    FirstPencilReferences (firstReferenceJ K) (firstReferenceP₀ K) (firstReferenceP₁ K) := by
  have kn : firstReferenceK K ≠ 0 := by
    have d := firstReferenceK_degree (K := K)
    intro z
    simp [z] at d
  refine ⟨firstReferenceJ_degree,?_,firstReferenceJ_weighted,firstReferenceP₀_weighted,
    firstReferenceP₁_identity,?_,?_,?_,?_,?_⟩
  · rw [firstReferenceP₀,natDegree_X_mul kn,firstReferenceK_degree]
  · rw [firstReferenceP₀,leadingCoeff_mul,leadingCoeff_X,one_mul,firstReferenceK_leading]
    norm_num
  · rw [firstReferenceJ_atZero]
    norm_num
  · rw [firstReferenceJ_atOne]
    exact zero_lt_one
  · simp [firstReferenceP₀,eval_mul]
  · have h : (firstReferenceP₁ K).eval 1=0 := by
      simp [firstReferenceP₁, eval_mul, eval_sub]
    rw [firstReferenceP₁_identity,eval_sub] at h
    exact sub_eq_zero.mp h

private theorem map_reference_ofFn {m : ℕ} (v : Fin m → ℚ) :
    (ofFn m v).map (Rat.castHom K)=
      ofFn m (fun i => (v i : K)) := by
  simp only [ofFn_eq_sum_monomial,Polynomial.map_sum,map_monomial,Rat.coe_castHom]

theorem firstReferenceJ_map :
    (firstReferenceJ ℚ).map (Rat.castHom K)=firstReferenceJ K := by
  rw [firstReferenceJ_ofFn (K:=ℚ),firstReferenceJ_ofFn (K:=K),map_reference_ofFn]
  congr 1
  funext i
  fin_cases i <;> norm_num

theorem firstReferenceK_map :
    (firstReferenceK ℚ).map (Rat.castHom K)=firstReferenceK K := by
  rw [firstReferenceK_ofFn (K:=ℚ),firstReferenceK_ofFn (K:=K),map_reference_ofFn]
  congr 1
  funext i
  fin_cases i <;> norm_num

theorem firstReferenceL_map :
    (firstReferenceL ℚ).map (Rat.castHom K)=firstReferenceL K := by
  rw [firstReferenceL_ofFn (K:=ℚ),firstReferenceL_ofFn (K:=K),map_reference_ofFn]
  congr 1
  funext i
  fin_cases i <;> norm_num

theorem firstReferenceP₀_map :
    (firstReferenceP₀ ℚ).map (Rat.castHom K)=firstReferenceP₀ K := by
  simp only [firstReferenceP₀,Polynomial.map_mul,map_X,firstReferenceK_map]

theorem firstReferenceP₁_map :
    (firstReferenceP₁ ℚ).map (Rat.castHom K)=firstReferenceP₁ K := by
  simp only [firstReferenceP₁,Polynomial.map_mul,Polynomial.map_sub,map_X,Polynomial.map_one,
    firstReferenceL_map]

end
end RKCert.ReviewedNative.WeakFourFirstOnly
