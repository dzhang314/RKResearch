module

public import RKCert.ReviewedNative.CausalDefectPrefix
import all RKCert.ReviewedNative.CausalDefectPrefix
import Lean.Elab.Tactic.Omega

public section

/-! # Diagonal-insensitive paid probes and causal pivots at a clean row

This module consumes the measured strict-prefix carrier without changing
it. Triangularity is required only for the actual recipient's row.
Private imports reuse its finite fibre and pivot proofs in proof bodies;
all exported statements use the public carrier on the actual tableau.
No stage order, width, diagonal equality or nonnegativity is assumed. -/
namespace RKResearch.Certified.Graded.DefectPrefix

open Polynomial OneOff
open scoped Classical Matrix

variable {K : Type*} [Field K] {s : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {k : Fin s}

/-- A lower-triangular recipient row splits into its literal earlier
off-row sum and its own diagonal entry, when earlier clean inputs vanish. -/
theorem mat_eq_off_sum_add_diag
    (hrow : ∀ i, k < i → A k i = 0) (v : Fin s → K)
    (z : ∀ i, i < k → g A i = 0 → v i = 0) :
    mat A v k = (∑ i ∈ earlierOffRows A k, A k i * v i) + A k k * v k := by
  classical
  have nk : k ∉ earlierOffRows A k :=
    fun h => (lt_irrefl k) (mem_earlierOffRows.mp h).1
  rw [mat_apply, Matrix.mulVec, dotProduct]
  have take : (∑ i ∈ insert k (earlierOffRows A k), A k i * v i) =
      ∑ i : Fin s, A k i * v i := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    have hik : i ≠ k := fun e => hi (Finset.mem_insert.mpr (Or.inl e))
    by_cases lt : i < k
    · have gi : g A i = 0 := by
        by_contra nz
        exact hi (Finset.mem_insert.mpr (Or.inr (mem_earlierOffRows.mpr ⟨lt,nz⟩)))
      rw [z i lt gi, mul_zero]
    · have gt : k < i := lt_of_le_of_ne (le_of_not_gt lt) (fun e => hik e.symm)
      rw [hrow i gt, zero_mul]
  rw [←take, Finset.sum_insert nk, add_comm]

/-- The diagonal contributes zero to the paid defect probe at an actual
g-clean recipient. These are the original clocks, defects and taps. -/
private theorem mat_defectColumn_eq_off_tests
    (hrow : ∀ i, k < i → A k i = 0) (clean : g A k = 0) (P : K[X]) :
    mat A (defectColumn A P) k =
      ∑ x ∈ earlierOffKnots A k, incomingOffResidue A k x * P.eval x := by
  calc
    _ = ∑ i ∈ earlierOffRows A k, A k i * defectColumn A P i := by
      have h := mat_eq_off_sum_add_diag hrow (defectColumn A P)
        (fun i _ gi => by simp only [defectColumn, diag_apply, gi, zero_mul])
      have dk : defectColumn A P k = 0 := by
        simp only [defectColumn, diag_apply, clean, zero_mul]
      rw [dk, mul_zero, add_zero] at h
      exact h
    _ = ∑ x ∈ earlierOffKnots A k, ∑ i ∈ offFibre A k x,
        A k i * defectColumn A P i :=
      (sum_off_fibres (A := A) (k := k) _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      rw [incomingOffResidue, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [defectColumn, diag_apply, evalNodes_apply, (mem_offFibre.mp hi).2, mul_assoc]

/-- Paid incoming probes at a clean lower-triangular recipient are
exactly the polynomial tests on the original earlier off residues. -/
theorem paidThrough_iff_off_residue_tests {d : ℕ}
    (hrow : ∀ i, k < i → A k i = 0) (clean : g A k = 0) :
    PaidThrough A k d ↔
      ∀ P : K[X], P.natDegree ≤ d →
        (∑ x ∈ earlierOffKnots A k, incomingOffResidue A k x * P.eval x) = 0 := by
  constructor
  · intro paid P hp
    rw [←mat_defectColumn_eq_off_tests hrow clean P]
    exact paid P hp
  · intro tests P hp
    rw [mat_defectColumn_eq_off_tests hrow clean P]
    exact tests P hp

/-- If all residues vanish, coherence makes the earlier off sum zero
against every clock-only observable. It is valid even if different
physical rows at one clock have different taps. -/
private theorem off_observable_eq_zero
    (coh : FibreCoherent A k)
    (hzero : ∀ x ∈ earlierOffKnots A k, incomingOffResidue A k x = 0)
    (f : K → K) :
    (∑ i ∈ earlierOffRows A k, A k i * f (nodes A i)) = 0 := by
  rw [←sum_off_fibres (A := A) (k := k) (fun i => A k i * f (nodes A i))]
  apply Finset.sum_eq_zero
  intro x hx
  have ximage : x ∈ (earlierOffRows A k).image (nodes A) := hx
  obtain ⟨l, hl, hlx⟩ := Finset.mem_image.mp ximage
  have factor : incomingOffResidue A k x =
      (∑ i ∈ offFibre A k x, A k i) * g A l := by
    rw [incomingOffResidue, Finset.sum_mul]
    refine Finset.sum_congr (f := fun i : Fin s => (A k i * g A i : K)) rfl ?_
    intro i hi
    obtain ⟨hi', hix⟩ := mem_offFibre.mp hi
    rw [coh hi' hl (hix.trans hlx.symm)]
  have z : (∑ i ∈ offFibre A k x, A k i) = 0 :=
    (mul_eq_zero.mp (factor.symm.trans (hzero x hx))).resolve_right
      (mem_earlierOffRows.mp hl).2
  calc
    _ = (∑ i ∈ offFibre A k x, A k i) * f x := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [(mem_offFibre.mp hi).2]
    _ = 0 := by rw [z, zero_mul]

/-- The unchanged triangular prefix carrier works for a clean recipient
of a general lower-triangular tableau. Either paid-row receipt suffices:
the sum of earlier off taps, or their clock-weighted sum. -/
theorem paid_prefix_pivots_of_off_mass_or_clock {d : ℕ}
    (hrow : ∀ i, k < i → A k i = 0) (clean : g A k = 0)
    (paid : PaidThrough A k d) (coh : FibreCoherent A k)
    (off : (∑ i ∈ earlierOffRows A k, A k i) ≠ 0 ∨
      (∑ i ∈ earlierOffRows A k, A k i * nodes A i) ≠ 0) :
    d + 2 ≤ (activeOffKnots A k).card ∧ Nonempty (TriangularPrefix A k (d + 2)) := by
  have enough : d + 2 ≤ (activeOffKnots A k).card := by
    by_contra short
    have cap : (activeOffKnots A k).card ≤ d + 1 := by omega
    have paidResidues := (paidThrough_iff_off_residue_tests hrow clean).mp paid
    have tests (P : K[X]) (hp : P.natDegree ≤ d) :
        (∑ x ∈ activeOffKnots A k, incomingOffResidue A k x * P.eval x) = 0 := by
      refine (Finset.sum_subset (active_subset (A := A) (k := k)) ?_).trans (paidResidues P hp)
      intro x hx no
      have z : incomingOffResidue A k x = 0 := by
        by_contra nz
        exact no (Finset.mem_filter.mpr ⟨hx,nz⟩)
      rw [z, zero_mul]
    have zeroActive := residues_eq_zero cap tests
    have zeroAll (x : K) (hx : x ∈ earlierOffKnots A k) : incomingOffResidue A k x = 0 := by
      by_contra nz
      exact nz (zeroActive x (Finset.mem_filter.mpr ⟨hx,nz⟩))
    rcases off with mass | clock
    · apply mass
      simpa only [mul_one] using off_observable_eq_zero coh zeroAll (fun _ => (1 : K))
    · exact clock (off_observable_eq_zero coh zeroAll id)
  exact ⟨enough, pivots_of_many
    (enough.trans (Finset.card_le_card (active_subset (A := A) (k := k))))⟩

section CharZero

variable [CharZero K]

/-- The real clock retains its diagonal term. With earlier clean
clocks zero, this equation displays exactly what the earlier off
clocks still have to pay at a clean recipient. -/
theorem off_clock_add_diag_eq_quad_of_clean
    (hrow : ∀ i, k < i → A k i = 0) (clean : g A k = 0)
    (earlier : ∀ i, i < k → g A i = 0 → nodes A i = 0) :
    (∑ i ∈ earlierOffRows A k, A k i * nodes A i) + A k k * nodes A k =
      (nodes A k)^2 / 2 :=
  (mat_eq_off_sum_add_diag hrow (nodes A) earlier).symm.trans
    (sub_eq_zero.mp ((g_apply A k).symm.trans clean))

/-- At the first clean row of a DIRK/SDIRK tableau with a nonzero
recipient diagonal, the earlier off mass or the earlier off clock
receipt is necessarily nonzero. Earlier clean zero-clock stages
are not covered by the first-clean hypothesis. -/
theorem off_mass_or_clock_of_first_clean
    (hrow : ∀ i, k < i → A k i = 0) (clean : g A k = 0) (diagonal : A k k ≠ 0)
    (first : ∀ i, i < k → g A i ≠ 0) :
    (∑ i ∈ earlierOffRows A k, A k i) ≠ 0 ∨
      (∑ i ∈ earlierOffRows A k, A k i * nodes A i) ≠ 0 := by
  by_cases mass : (∑ i ∈ earlierOffRows A k, A k i) = 0
  · right
    intro clock
    have rowMass := mat_eq_off_sum_add_diag hrow (fun _ => (1 : K))
      (fun i hi gi => (first i hi gi).elim)
    have node : mat A (fun _ => (1 : K)) k = nodes A k := rfl
    have cEq : nodes A k = A k k := by
      simpa only [node, mul_one, mass, zero_add] using rowMass
    have r := off_clock_add_diag_eq_quad_of_clean hrow clean
      (fun i hi gi => (first i hi gi).elim)
    have half : A k k * A k k = (A k k)^2 / 2 := by
      simpa only [clock, zero_add, cEq] using r
    have twice : (A k k * A k k) * (2 : K) = A k k * A k k := by
      simpa only [pow_two] using (eq_div_iff (two_ne_zero : (2 : K) ≠ 0)).mp half
    have add : (A k k * A k k) + (A k k * A k k) = (A k k * A k k) + 0 := by
      rw [add_zero, ←mul_two]
      exact twice
    exact (mul_ne_zero diagonal diagonal) (add_left_cancel add)
  · exact Or.inl mass

/-- In particular, independently earned probes and coherence force all
these pivots before the first actual clean row of a nonzero-diagonal
DIRK method, without a clock nonresonance assumption. -/
theorem paid_prefix_pivots_of_first_clean_diagonal {d : ℕ}
    (hrow : ∀ i, k < i → A k i = 0) (clean : g A k = 0) (diagonal : A k k ≠ 0)
    (first : ∀ i, i < k → g A i ≠ 0) (paid : PaidThrough A k d) (coh : FibreCoherent A k) :
    d + 2 ≤ (activeOffKnots A k).card ∧ Nonempty (TriangularPrefix A k (d + 2)) :=
  paid_prefix_pivots_of_off_mass_or_clock hrow clean paid coh
    (off_mass_or_clock_of_first_clean hrow clean diagonal first)

end CharZero

end RKResearch.Certified.Graded.DefectPrefix
