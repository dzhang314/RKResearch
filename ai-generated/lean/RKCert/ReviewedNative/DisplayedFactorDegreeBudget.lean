module

public import RKCert.ReviewedNative.FiniteOrderedSignWindows

@[expose] public section

/-! # Degree charge for a displayed factor of fixed sign -/

namespace RKCert.ReviewedNative.FiniteOrderedSigns

open Polynomial RKCert.ReviewedNative.PositiveRule19

noncomputable section

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- A displayed fixed-sign factor consumes degree in the untested part
of a polynomial with paid orthogonality. The quotient is the test:
if it were paid, the integrand would have fixed sign and a live sample.
No splitting of the polynomial is assumed. -/
theorem displayed_factor_degree_budget {U M F G : K[X]} {d : ℕ}
    (mn : M ≠ 0) (factor : M = F * G)
    (weightPos : ∀ i : Fin 19, 0 < U.eval (intervalPoint (0 : K) 1 i))
    (fixedSign :
      (∀ i : Fin 19, 0 ≤ F.eval (intervalPoint (0 : K) 1 i)) ∨
      (∀ i : Fin 19, F.eval (intervalPoint (0 : K) 1 i) ≤ 0))
    (pay : U.natDegree + M.natDegree + d < 19)
    (orth : ∀ H : K[X], H.natDegree ≤ d →
      integral 0 1 (U * M * H) = 0) :
    d + F.natDegree < M.natDegree := by
  have unit : (0 : K) < 1 := zero_lt_one
  have un : U ≠ 0 := by
    intro h
    have h0 := weightPos (0 : Fin 19)
    rw [h, eval_zero] at h0
    exact (lt_irrefl (0 : K)) h0
  have fn : F ≠ 0 := fun h => mn (by rw [factor, h, zero_mul])
  have gn : G ≠ 0 := fun h => mn (by rw [factor, h, mul_zero])
  have degreeM : M.natDegree = F.natDegree + G.natDegree := by
    rw [factor, natDegree_mul fn gn]
  by_contra no
  have boundM : M.natDegree ≤ d + F.natDegree := le_of_not_gt no
  have gd : G.natDegree ≤ d := by
    rw [degreeM, Nat.add_comm d F.natDegree] at boundM
    exact Nat.le_of_add_le_add_left boundM
  let test : K[X] := U * M * G
  have testNonzero : test ≠ 0 := mul_ne_zero (mul_ne_zero un mn) gn
  have testBound : test.natDegree ≤ U.natDegree + M.natDegree + G.natDegree := by
    dsimp only [test]
    exact natDegree_mul_le_of_le (natDegree_mul_le (p := U) (q := M)) le_rfl
  have testDegree : test.natDegree < 19 :=
    (testBound.trans (Nat.add_le_add_left gd (U.natDegree + M.natDegree))).trans_lt pay
  have testZero : integral 0 1 test = 0 := orth G gd
  have evalTest (i : Fin 19) :
      test.eval (intervalPoint (0 : K) 1 i) =
        U.eval (intervalPoint (0 : K) 1 i) *
          F.eval (intervalPoint (0 : K) 1 i) *
          (G.eval (intervalPoint (0 : K) 1 i))^2 := by
    simp only [test, factor, eval_mul, pow_two, mul_assoc]
  obtain ⟨i, live⟩ := exists_nonzero_grid_sample unit testNonzero testDegree
  rcases fixedSign with pos | neg
  · have nonneg (j : Fin 19) : 0 ≤ test.eval (intervalPoint (0 : K) 1 j) := by
      rw [evalTest j]
      exact mul_nonneg (mul_nonneg (weightPos j).le (pos j)) (sq_nonneg _)
    have strict : 0 < test.eval (intervalPoint (0 : K) 1 i) :=
      lt_of_le_of_ne (nonneg i) live.symm
    exact (integral_pos_of_grid_samples unit testDegree.le nonneg ⟨i, strict⟩).ne'
      testZero
  · have nonpos (j : Fin 19) : test.eval (intervalPoint (0 : K) 1 j) ≤ 0 := by
      rw [evalTest j]
      exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (weightPos j).le (neg j)) (sq_nonneg _)
    have negDegree : (-test).natDegree ≤ 19 := by
      simpa only [natDegree_neg] using testDegree.le
    have nonneg (j : Fin 19) : 0 ≤ (-test).eval (intervalPoint (0 : K) 1 j) := by
      rw [eval_neg]
      exact neg_nonneg.mpr (nonpos j)
    have strict : 0 < (-test).eval (intervalPoint (0 : K) 1 i) := by
      rw [eval_neg]
      exact neg_pos.mpr (lt_of_le_of_ne (nonpos i) live)
    have negZero : integral 0 1 (-test) = 0 := by
      rw [map_neg, testZero, neg_zero]
    exact (integral_pos_of_grid_samples unit negDegree nonneg ⟨i, strict⟩).ne'
      negZero

end

end RKCert.ReviewedNative.FiniteOrderedSigns
