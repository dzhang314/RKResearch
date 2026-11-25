module

import RKCert.ReviewedNative.HiddenClockLeakage
import Mathlib.Basic.Real.Basic

/-! Typed source probes only; this file is not a replay receipt. -/

open Polynomial RKResearch RKResearch.ClockLeakage
open RKCert.ReviewedNative.PositiveRule19

section

variable {s p : ℕ} {A : Matrix (Fin s) (Fin s) ℝ} {b : Fin s → ℝ}

/-- Actual real ERK, not a replacement matrix or predicate. The local
conclusion needs the hidden leakage even though the diagonal is zero. -/
example (ho : HasOrder p A b) (strict : ∀ i j, i ≤ j → A i j = 0)
    {T : Finset ℝ} {t : ℝ} (ht : t ∈ T) (F : ℝ[X])
    (cover : ∀ x, x ∉ T → outputMass A b x = 0)
    (paid : F.natDegree + T.card + 1 ≤ p) (live : outputMass A b t ≠ 0)
    (strictZero : strictColumn A b t (F.comp (1 - X)) = 0)
    (leakZero : hiddenLeakage A b T (visibleSelector T t) (F.comp (1 - X)) = 0) :
    integral 0 (1 - t) F = 0 :=
  ho.erk_visibleClock_reflected_local_zero strict ht F cover paid live strictZero leakZero

/-- Actual real DIRK with arbitrary lower triangle and an actual stop
root. The separately supplied signed atom proof is the only source of
the second conjunct, not the root, row leakage, or tree order. -/
example (ho : HasOrder p A b) (lower : A.IsLowerTriangular)
    {T : Finset ℝ} {t : ℝ} (ht : t ∈ T) (F : ℝ[X])
    (cover : ∀ x, x ∉ T → outputMass A b x = 0)
    (paid : F.natDegree + T.card + 1 ≤ p) (live : outputMass A b t ≠ 0)
    (stopRoot : F.eval (1 - t) = 0)
    (strictZero : strictColumn A b t (F.comp (1 - X)) = 0)
    (leakZero : hiddenLeakage A b T (visibleSelector T t) (F.comp (1 - X)) = 0)
    (μ : ℝ → ℝ) (independentAtomErasure : μ (1 - t) = 0) :
    integral 0 (1 - t) F = 0 ∧ μ (1 - t) = 0 :=
  ⟨ho.dirk_visibleClock_reflected_local_zero lower ht F cover paid live stopRoot strictZero leakZero,
    independentAtomErasure⟩

end

#check @RKResearch.ClockLeakage.paid_rowFunctional_test
#check @RKResearch.HasOrder.clockColumn_hiddenLeakage_affine
#check @RKResearch.HasOrder.visibleClock_reflected_hiddenLeakage_affine
#check @RKResearch.HasOrder.visibleClock_reflected_hiddenLeakage_eq
#check @RKResearch.ClockLeakage.hiddenLeakage_eq_zero_of_tested_rows
#check @RKResearch.HasOrder.visibleClock_reflected_zero_iff
#check @RKResearch.HasOrder.erk_visibleClock_reflected_local_zero
#check @RKResearch.HasOrder.dirk_visibleClock_reflected_local_zero

#print axioms RKResearch.HasOrder.clockColumn_hiddenLeakage_affine
#print axioms RKResearch.HasOrder.erk_visibleClock_reflected_local_zero
#print axioms RKResearch.HasOrder.dirk_visibleClock_reflected_local_zero
