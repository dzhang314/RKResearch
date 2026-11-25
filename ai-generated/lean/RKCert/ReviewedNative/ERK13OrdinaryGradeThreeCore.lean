module

public import RKCert.ReviewedNative.ERK13OrdinaryShiftPurity
public import RKCert.ReviewedNative.ERK13OrdinaryCubicProfile

@[expose] public section

/-! # Native order-thirteen grade three lies in the actual invariant core -/
namespace RKResearch.Certified.Graded.ERK13NativeFirst

open RKResearch Polynomial Reverse RKCert.OneEscape
open scoped Classical Matrix
noncomputable section
variable {K : Type*} [Field K] [CharZero K]
variable {A : Matrix (Fin 19) (Fin 19) K} {b : Fin 19→K}
variable {G : K[X]} {U : Submodule K (Fin 19→K)} {w : Fin 19→K} {r : ℕ}

theorem ordinary_grade_three_le_core (ha : ∀ i j,i≤j → A i j=0)
    (ho : HasOrder 13 A b) (seed : firstSeed A b≠0)
    (H : OrdinaryStaircase A b G r U w) : zeroSpace A 3≤U := by
  intro v hv
  by_contra outside
  obtain ⟨vstable,P,pn,pd,fit⟩ := ordinary_grade_three_profile ha ho seed H hv outside
  exact ordinary_cubic_profile_impossible ha ho
    (PolySeparated.of_coeff (coeff_separated ho (q:=6) (by decide)))
    (H.paidHead.head.coreInside.trans (zeroSpace_mono A (by decide)))
    H.paidHead.head.coreStable vstable H.headSeven.le hv pn pd fit

end
end RKResearch.Certified.Graded.ERK13NativeFirst
