module

import RKCert.ReviewedNative.HiddenClockMomentLadder
import Mathlib.Basic.Real.Basic

/-! Unrun typed source probes. No inference about a signed stop atom is
made from the finite support comparison. -/

open Polynomial RKResearch RKResearch.ClockLeakage
open RKCert.Endpoint RKCert.ReviewedNative.FiniteClockMoments
open RKCert.ReviewedNative.PositiveRule19
open scoped BigOperators Classical

section FiniteLaw
variable {K : Type*} [Field K] {H E : Finset K} {q : ℕ}

example (mass : K → K) (apart : ∀ x ∈ H, x ∉ E) (size : H.card ≤ q)
    (tests : ∀ k : ℕ, k < q → (∑ x ∈ H, (mass x * (nodalHull E).eval x) * x ^ k) = 0) :
    ∀ x ∈ H, mass x = 0 :=
  mass_zero_of_tilted_tests mass apart size ((tiltedTests_iff_sums H E mass q).2 tests)

end FiniteLaw

section ActualTableau
variable {s p d : ℕ} {A : Matrix (Fin s) (Fin s) ℝ} {b : Fin s → ℝ}

example (ho : HasOrder p A b) (strict : ∀ i j, i ≤ j → A i j = 0)
    {T S : Finset ℝ} {a : ℝ} (ha : a ∈ T) (sub : S ⊆ T) (F : ℝ[X])
    (degree : F.natDegree ≤ d) (budget : d + T.card + 1 ≤ p)
    (cover : ∀ x, x ∉ T → outputMass A b x = 0) (live : outputMass A b a ≠ 0)
    (good : ∀ t ∈ S, groupedColumn A b t (F.comp (1 - X)) =
      outputMass A b t * integral t 1 (F.comp (1 - X)))
    (size : (effectiveHiddenClocks A b T (F.comp (1 - X))).card ≤
      p - d - T.card - 1 + S.card)
    (strictZero : strictColumn A b a (F.comp (1 - X)) = 0) : integral 0 (1 - a) F = 0 :=
  ho.erk_reflected_local_zero_of_hidden_ladder strict ha sub F degree budget cover live good size strictZero

example (ho : HasOrder p A b) (lower : A.IsLowerTriangular)
    {T S : Finset ℝ} {a : ℝ} (ha : a ∈ T) (sub : S ⊆ T) (F : ℝ[X])
    (degree : F.natDegree ≤ d) (budget : d + T.card + 1 ≤ p)
    (cover : ∀ x, x ∉ T → outputMass A b x = 0) (live : outputMass A b a ≠ 0)
    (good : ∀ t ∈ S, groupedColumn A b t (F.comp (1 - X)) =
      outputMass A b t * integral t 1 (F.comp (1 - X)))
    (size : (effectiveHiddenClocks A b T (F.comp (1 - X))).card ≤
      p - d - T.card - 1 + S.card)
    (stopRoot : F.eval (1 - a) = 0) (strictZero : strictColumn A b a (F.comp (1 - X)) = 0)
    (mu : ℝ → ℝ) (independentAtomErasure : mu (1 - a) = 0) :
    integral 0 (1 - a) F = 0 ∧ mu (1 - a) = 0 :=
  ⟨ho.dirk_reflected_local_zero_of_hidden_ladder lower ha sub F degree budget cover live good size
    stopRoot strictZero, independentAtomErasure⟩

end ActualTableau

#check @RKCert.ReviewedNative.FiniteClockMoments.mass_zero_of_tilted_tests
#check @RKCert.ReviewedNative.FiniteClockMoments.zero_on_stops_iff_tilted_tests
#check @RKCert.ReviewedNative.FiniteClockMoments.moment_eq_of_same_paid_values
#check @RKResearch.HasOrder.hiddenClock_momentLaw
#check @RKResearch.HasOrder.hiddenClock_ladder_iff
#check @RKResearch.HasOrder.hiddenClock_zero_of_low_support
#check @RKResearch.HasOrder.erk_reflected_local_zero_of_hidden_ladder
#check @RKResearch.HasOrder.dirk_reflected_local_zero_of_hidden_ladder

#print axioms RKCert.ReviewedNative.FiniteClockMoments.mass_zero_of_tilted_tests
#print axioms RKResearch.HasOrder.hiddenClock_ladder_iff
#print axioms RKResearch.HasOrder.erk_reflected_local_zero_of_hidden_ladder
#print axioms RKResearch.HasOrder.dirk_reflected_local_zero_of_hidden_ladder
