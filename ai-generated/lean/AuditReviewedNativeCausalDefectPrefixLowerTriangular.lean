import RKCert.ReviewedNative.CausalDefectPrefixLowerTriangular

/-! Standalone typed client of the actual generic lower-triangular prefix. -/
open Polynomial
open RKResearch.Certified.Graded RKResearch.Certified.Graded.OneOff
open RKResearch.Certified.Graded.DefectPrefix
open scoped Classical Matrix

section
variable {K : Type*} [Field K] {s d : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {k : Fin s}

example (hrow : ∀ i, k < i → A k i = 0) (v : Fin s → K)
    (z : ∀ i, i < k → g A i = 0 → v i = 0) :
    mat A v k = (∑ i ∈ earlierOffRows A k, A k i * v i) + A k k * v k :=
  mat_eq_off_sum_add_diag hrow v z

example (hrow : ∀ i, k < i → A k i = 0) (clean : g A k = 0) :
    (∀ P : K[X], P.natDegree ≤ d → mat A (fun i => g A i * P.eval (nodes A i)) k = 0) ↔
      ∀ P : K[X], P.natDegree ≤ d →
        (∑ x ∈ earlierOffKnots A k, incomingOffResidue A k x * P.eval x) = 0 := by
  have col (P : K[X]) : defectColumn A P = (fun i => g A i * P.eval (nodes A i)) := by
    funext i
    simp only [defectColumn, diag_apply, evalNodes_apply]
  have tests := paidThrough_iff_off_residue_tests (d := d) hrow clean
  constructor
  · intro paid
    apply tests.mp
    intro P hp
    rw [col P]
    exact paid P hp
  · intro probes P hp
    have eq := tests.mpr probes P hp
    rwa [col P] at eq

example (hrow : ∀ i, k < i → A k i = 0) (clean : g A k = 0)
    (paid : PaidThrough A k d) (coh : FibreCoherent A k)
    (off : (∑ i ∈ earlierOffRows A k, A k i) ≠ 0 ∨
      (∑ i ∈ earlierOffRows A k, A k i * nodes A i) ≠ 0) :
    d + 2 ≤ (activeOffKnots A k).card ∧ Nonempty (TriangularPrefix A k (d + 2)) :=
  paid_prefix_pivots_of_off_mass_or_clock hrow clean paid coh off

variable [CharZero K]

example (hrow : ∀ i, k < i → A k i = 0) (clean : g A k = 0)
    (earlier : ∀ i, i < k → g A i = 0 → nodes A i = 0) :
    (∑ i ∈ earlierOffRows A k, A k i * nodes A i) + A k k * nodes A k =
      (nodes A k)^2 / 2 :=
  off_clock_add_diag_eq_quad_of_clean hrow clean earlier

example (hrow : ∀ i, k < i → A k i = 0) (clean : g A k = 0) (diagonal : A k k ≠ 0)
    (first : ∀ i, i < k → g A i ≠ 0) :
    (∑ i ∈ earlierOffRows A k, A k i) ≠ 0 ∨
      (∑ i ∈ earlierOffRows A k, A k i * nodes A i) ≠ 0 :=
  off_mass_or_clock_of_first_clean hrow clean diagonal first

example (hrow : ∀ i, k < i → A k i = 0) (clean : g A k = 0) (diagonal : A k k ≠ 0)
    (first : ∀ i, i < k → g A i ≠ 0) (paid : PaidThrough A k d) (coh : FibreCoherent A k) :
    d + 2 ≤ (activeOffKnots A k).card ∧ Nonempty (TriangularPrefix A k (d + 2)) :=
  paid_prefix_pivots_of_first_clean_diagonal hrow clean diagonal first paid coh

end

#print axioms RKResearch.Certified.Graded.DefectPrefix.mat_eq_off_sum_add_diag
#print axioms RKResearch.Certified.Graded.DefectPrefix.paidThrough_iff_off_residue_tests
#print axioms RKResearch.Certified.Graded.DefectPrefix.paid_prefix_pivots_of_off_mass_or_clock
#print axioms RKResearch.Certified.Graded.DefectPrefix.off_clock_add_diag_eq_quad_of_clean
#print axioms RKResearch.Certified.Graded.DefectPrefix.off_mass_or_clock_of_first_clean
#print axioms RKResearch.Certified.Graded.DefectPrefix.paid_prefix_pivots_of_first_clean_diagonal
