module

public import RKCert.ReviewedNative.ERK8FourOffPaidExclusion
public import RKCert.ReviewedNative.ERK8CharElevenStageFloor

import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Ideal.Quotient.Basic

@[expose] public section

/-! # The universal native stage minimum for explicit order eight -/
namespace RKResearch.Certified.ERK8Universal

open RKResearch StagePadding FiniteRootedTree Graded
open Graded.ERK8PaidField Graded.OneOff.EightPaid Graded.FourOffNewton Ideal.Quotient
open scoped Matrix

variable {K : Type*} [Field K]

theorem no_order8_fin10 (A : Matrix (Fin 10) (Fin 10) K) (b : Fin 10→K)
    (ha : ERK A) (ho : HasOrder 8 A b) : False := by
  by_cases p : (11:K)=0
  · exact ERK8CharElevenFloor.no_order8_fin10 p A b ha ho
  obtain ⟨_,one|four⟩ := order8_paid_one_or_four_with_horizon ha ho p
  · exact no_order8_one_off ha ho one
  · exact no_four_off_paid_outside11 ha ho p four

theorem stages_at_least_eleven_field {s : ℕ} {A : Matrix (Fin s) (Fin s) K} {b : Fin s→K}
    (ha : ERK A) (ho : HasOrder 8 A b) : 11≤s :=
  Nat.succ_le_of_lt (strict_stages_gt_of_exact_exclusion no_order8_fin10 ha ho)

variable {R : Type*} [CommRing R] [Nontrivial R]

/-- The reviewed order equations and strictness specialize to any
maximal residue field. Neither a domain nor a characteristic condition is
needed on the original nontrivial ring. -/
theorem stages_at_least_eleven {s : ℕ} {A : Matrix (Fin s) (Fin s) R} {b : Fin s→R}
    (ha : ERK A) (ho : HasOrder 8 A b) : 11≤s := by
  obtain ⟨I,hI⟩ := Ideal.exists_maximal (α:=R)
  let := hI
  let := Ideal.Quotient.field I
  let f := Ideal.Quotient.mk I
  have strict : ERK (A.map f) := by
    intro i j h
    change f (A i j)=0
    rw [ha h,map_zero]
  exact stages_at_least_eleven_field strict (HasOrder.map ho f)

/-- Exact order eight exists at width s precisely when eleven
stages fit and the literal order-eight factorial is a ring unit. -/
theorem exact_order_eight_exists_iff (s : ℕ) :
    (∃ A : Matrix (Fin s) (Fin s) R, ∃ b : Fin s→R,
      ERK A ∧ HasOrder 8 A b ∧ ¬ HasOrder 9 A b) ↔
      11≤s ∧ IsUnit (Nat.factorial 8:R) := by
  refine ⟨?_,?_⟩
  · rintro ⟨A,b,ha,ho,_⟩
    have t := ho (tallTree 8) (by decide)
    have f : ((tallTree 8).factorial:R)=(Nat.factorial 8:R) := by norm_cast
    exact ⟨stages_at_least_eleven ha ho,IsUnit.of_mul_eq_one _ (f ▸ t)⟩
  · rintro ⟨h,isUnit8⟩
    obtain ⟨A,b,ha,ho,fail⟩ := ERK8FactorialEleven.exists_exact_order_eight isUnit8
    exact ⟨zeroPadMatrix A s,zeroPadVec b s,(zeroPadMatrix_strict_iff h).mpr ha,
      (hasOrder_zeroPad_iff h).mpr ho,fun h9=>fail ((hasOrder_zeroPad_iff h).mp h9)⟩

end RKResearch.Certified.ERK8Universal

#print axioms RKResearch.Certified.ERK8Universal.no_order8_fin10
#print axioms RKResearch.Certified.ERK8Universal.stages_at_least_eleven
#print axioms RKResearch.Certified.ERK8Universal.exact_order_eight_exists_iff
