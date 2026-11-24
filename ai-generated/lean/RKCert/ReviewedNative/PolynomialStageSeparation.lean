module
public import RKCert.ReviewedNative.GradedSeparation
public import RKCert.ReviewedNative.GradedPrimitives
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Algebra.Polynomial.Roots

@[expose] public section

/-! # Polynomial form of the native finite coefficient separation -/
namespace RKResearch.Certified.Graded
open Polynomial
open scoped Matrix

variable {ι K : Type*} [Fintype ι] [Field K] {A : Matrix ι ι K} {q : ℕ}

/-- Stage polynomial evaluation in the canonical finite coefficient basis. -/
theorem evalNodes_eq_coeffEval (A : Matrix ι ι K) (P : K[X]) (hp : P.natDegree ≤ q) :
    evalNodes A P = coeffEval A q (fun j => P.coeff j.val) := by
  ext i
  rw [evalNodes_apply, eval_eq_sum_range' (Nat.lt_succ_of_le hp)]
  simp only [coeffEval_apply, Finset.sum_apply, normTree_clockTree, Pi.smul_apply, smul_eq_mul]
  rw [← Fin.sum_univ_eq_sum_range]

/-- No nonzero polynomial through degree `q` has a stage evaluation
inside the homogeneous defect space. -/
def PolySeparated (A : Matrix ι ι K) (q : ℕ) : Prop :=
  ∀ P : K[X], P.natDegree ≤ q → evalNodes A P ∈ zeroSpace A q → P = 0

theorem PolySeparated.of_coeff
    (sep : ∀ a, coeffEval A q a ∈ zeroSpace A q → a = 0) : PolySeparated A q := by
  intro P hp hv
  rw [evalNodes_eq_coeffEval A P hp] at hv
  have z := sep _ hv
  ext n
  rw [coeff_zero]
  by_cases h : n ≤ q
  · exact congrFun z (⟨n, Nat.lt_succ_of_le h⟩ : Fin (q+1))
  · exact coeff_eq_zero_of_natDegree_lt (hp.trans_lt (Nat.lt_of_not_ge h))

theorem PolySeparated.mono (sep : PolySeparated A q) {r : ℕ} (hr : r ≤ q) :
    PolySeparated A r :=
  fun P hP hv => sep P (hP.trans hr) (zeroSpace_mono A hr hv)

theorem PolySeparated.nodes_not_mem (sep : PolySeparated A q) (hq : 1 ≤ q) :
    nodes A ∉ zeroSpace A q := by
  intro hz
  have ev : evalNodes A (X : K[X]) = nodes A := by
    ext i
    simp
  exact X_ne_zero (sep _ (by simpa using hq) (ev.symm ▸ hz))

/-- A degree-`q` separating map rules out covering all physical stage
nodes by `q` or fewer clocks, allowing arbitrary multiplicities. -/
theorem PolySeparated.knots_not_cover (sep : PolySeparated A q) (S : Finset K)
    (hs : S.card ≤ q) : ¬ ∀ i, nodes A i ∈ S := by
  intro hall
  let H : K[X] := ∏ r ∈ S, (X - C r)
  have mh : H.Monic := monic_prod_X_sub_C id S
  have d : H.natDegree ≤ q := by
    unfold H
    rw [natDegree_prod_of_monic S (fun r => X - C r) (fun r _ => monic_X_sub_C r)]
    simpa using hs
  have v : evalNodes A H = 0 := by
    ext i
    simp only [evalNodes_apply, H, eval_prod, eval_sub, eval_X, eval_C, Pi.zero_apply]
    exact Finset.prod_eq_zero (hall i) (sub_self _)
  exact mh.ne_zero (sep H d (v.symm ▸ (zeroSpace A q).zero_mem))

end RKResearch.Certified.Graded
