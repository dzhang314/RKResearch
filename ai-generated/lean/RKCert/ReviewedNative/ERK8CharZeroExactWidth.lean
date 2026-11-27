module

public import RKCert.ReviewedNative.ERK8CharZeroStageFloor
public import RKCert.ReviewedNative.ERK8FactorialEleven

@[expose] public section

/-! # Exact ERK order eight at every characteristic-zero width -/
namespace RKResearch.Certified.ERK8CharZero

open RKResearch StagePadding FiniteRootedTree
open scoped Matrix

universe u

variable {R : Type u} [CommRing R] [CharZero R]

/-- A native characterization of every width that attains exact order
eight in characteristic zero, including rings with zero divisors. -/
theorem exact_order_eight_exists_iff (s : ℕ) :
    (∃ A : Matrix (Fin s) (Fin s) R, ∃ b : Fin s→R,
      ERK A ∧ HasOrder 8 A b ∧ ¬ HasOrder 9 A b) ↔
      11≤s ∧ IsUnit (Nat.factorial 8:R) := by
  refine ⟨?_,?_⟩
  · rintro ⟨A,b,ha,ho,_⟩
    have t := ho (tallTree 8) (by decide)
    have e : ((tallTree 8).factorial:R)=(Nat.factorial 8:R) := by norm_cast
    exact ⟨stages_at_least_eleven ha ho,IsUnit.of_mul_eq_one _ (e ▸ t)⟩
  · rintro ⟨h,isUnit8⟩
    obtain ⟨A,b,ha,ho,fail⟩ := ERK8FactorialEleven.exists_exact_order_eight isUnit8
    exact ⟨zeroPadMatrix A s,zeroPadVec b s,(zeroPadMatrix_strict_iff h).mpr ha,
      (hasOrder_zeroPad_iff h).mpr ho,fun h9=>fail ((hasOrder_zeroPad_iff h).mp h9)⟩

end RKResearch.Certified.ERK8CharZero

#print axioms RKResearch.Certified.ERK8CharZero.exact_order_eight_exists_iff
