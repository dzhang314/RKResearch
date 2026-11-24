module

public import RKCert.ReviewedNative.NonsingularDIRKStageFloor
import Mathlib.Tactic.Ring

public section

/-! # Exact closed form of the native parity stage floor

The penultimate and last parity counts differ by at most one. Removing
the two end grades in order `p+2` shifts each interior width down by
one and swaps the parity counts. This evaluates the *existing* lower
bound exactly, without imposing any finite cutoff on the order.
-/

namespace RKResearch.Certified.Graded

private theorem parityCensus_shift (p : ℕ) :
    ∀ a, a+1 ≤ p →
      parityCensus (p+2) (a+1) = parityCensus p a + (a+1)/2 + 1
  | 0, h => by simp only [parityCensus]; omega
  | 1, h => by simp only [parityCensus]; omega
  | a+2, h => by
      simp only [parityCensus]
      rw [parityCensus_shift p a (by omega)]
      omega

private abbrev lastCount (p : ℕ) := parityCensus p (p-1)
private abbrev penultimateCount (p : ℕ) := parityCensus p (p-2)

private theorem parityCounts_step (p : ℕ) (hp : 2 ≤ p) :
    lastCount (p+2) = penultimateCount p + (p-1)/2 + 2 ∧
      penultimateCount (p+2) = lastCount p + p/2 + 1 := by
  constructor
  · change parityCensus (p+2) (p+2-1) = _
    rw [show p+2-1 = (p-1)+2 by omega, parityCensus]
    have h := parityCensus_shift p (p-2) (by omega)
    rw [show p-2+1 = p-1 by omega] at h
    rw [h]
    simp only [penultimateCount]
    omega
  · change parityCensus (p+2) (p+2-2) = _
    have h := parityCensus_shift p (p-1) (by omega)
    rwa [show p-1+1 = p+2-2 by omega, show (p+2-2)/2 = p/2 by omega] at h

private theorem squarePacket_step (p : ℕ) :
    (p+2+1)^2/4 = (p+1)^2/4 + (p+2) := by
  rw [show (p+2+1)^2 = (p+1)^2 + 4*(p+2) by ring]
  omega

private theorem parityCounts_balance :
    ∀ p, 2 ≤ p → lastCount p + penultimateCount p = (p+1)^2/4 ∧
      penultimateCount p ≤ lastCount p ∧ lastCount p ≤ penultimateCount p + p%2
  | 0, h => by omega
  | 1, h => by omega
  | 2, _ => by decide
  | 3, _ => by decide
  | p+4, _ => by
      change lastCount (p+2+2) + penultimateCount (p+2+2) = (p+2+2+1)^2/4 ∧
        penultimateCount (p+2+2) ≤ lastCount (p+2+2) ∧
          lastCount (p+2+2) ≤ penultimateCount (p+2+2) + (p+2+2)%2
      obtain ⟨sum, lo, hi⟩ := parityCounts_balance (p+2) (by omega)
      obtain ⟨last, next⟩ := parityCounts_step (p+2) (by omega)
      rw [last, next, squarePacket_step, ← sum]
      exact ⟨by omega, by omega, by omega⟩

/-- The recursive floor equals `ceil(floor((p+1)²/4)/2)` at every positive order.
All arithmetic here is natural-number arithmetic, not coefficient-field arithmetic. -/
theorem nonsingularStageFloor_eq_quadratic (p : ℕ) (hp : 0 < p) :
    nonsingularStageFloor p = ((p+1)^2/4+1)/2 := by
  by_cases h : p = 1
  · subst p
    decide
  · obtain ⟨sum, lo, hi⟩ := parityCounts_balance p (by omega)
    rw [nonsingularStageFloor, max_eq_left lo, ← sum]
    omega

end RKResearch.Certified.Graded

namespace RKResearch

open Certified.Graded

/-- An arbitrary field and a lower triangular tableau with nonzero diagonal
suffice for the quadratic stage floor at every achieved positive order. -/
theorem HasOrder.nonsingular_quadratic_stage_floor_field {K : Type*} [Field K] {s p : ℕ}
    {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
    (ho : HasOrder A b p) (ha : A.IsLowerTriangular) (hn : ∀ i, A i i ≠ 0) (hp : 0 < p) :
    ((p+1)^2/4+1)/2 ≤ s := by
  rw [← nonsingularStageFloor_eq_quadratic p hp]
  exact nonsingular_stageFloor_field ho ha hn hp

/-- Over a nontrivial commutative ring the same bound holds with unit diagonal,
again without a cap on order or a separate characteristic hypothesis. -/
theorem HasOrder.nonsingular_quadratic_stage_floor {R : Type*} [CommRing R] [Nontrivial R] {s p : ℕ}
    {A : Matrix (Fin s) (Fin s) R} {b : Fin s → R}
    (ho : HasOrder A b p) (ha : A.IsLowerTriangular) (hu : ∀ i, IsUnit (A i i)) (hp : 0 < p) :
    ((p+1)^2/4+1)/2 ≤ s := by
  rw [← nonsingularStageFloor_eq_quadratic p hp]
  exact ho.nonsingular_stageFloor ha hu hp

end RKResearch

