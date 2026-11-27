module

public import RKCert.ReviewedNative.ERK8PaidOneOffFin10
public import RKCert.ReviewedNative.ERK8CharElevenFourExclusion
public import RKCert.ReviewedNative.StagePadding
public import RKCert.ReviewedNative.ERK8FactorialEleven
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Nilpotent.Defs

@[expose] public section

/-! # The native ERK8 stage minimum in characteristic eleven and its nilpotent thickenings -/
namespace RKResearch.Certified.ERK8CharElevenFloor

open RKResearch Graded Graded.OneOff.EightPaid StagePadding FiniteRootedTree
open Ideal.Quotient
open scoped Matrix

variable {K : Type*} [Field K]

theorem no_order8_fin10 (p : (11:K)=0)
    (A : Matrix (Fin 10) (Fin 10) K) (b : Fin 10→K)
    (ha : ERK A) (ho : HasOrder 8 A b) : False :=
  no_order8_one_off ha ho (Graded.ERK8CharEleven.order8_char11_only_one_off ha ho p)

theorem stages_at_least_eleven_field {s : ℕ} {A : Matrix (Fin s) (Fin s) K} {b : Fin s→K}
    (p : (11:K)=0) (ha : ERK A) (ho : HasOrder 8 A b) : 11≤s :=
  Nat.succ_le_of_lt (strict_stages_gt_of_exact_exclusion (no_order8_fin10 p) ha ho)

variable {R : Type*} [CommRing R] [Nontrivial R]

/-- The literal lower bound survives arbitrary nilpotent extensions
of characteristic eleven, including rings of any characteristic 11^k. -/
theorem stages_at_least_eleven_of_nilpotent {s : ℕ} {A : Matrix (Fin s) (Fin s) R}
    {b : Fin s→R} (p : IsNilpotent (11:R)) (ha : ERK A) (ho : HasOrder 8 A b) : 11≤s := by
  obtain ⟨I,hI⟩ := Ideal.exists_maximal (α:=R)
  let := hI
  let := Ideal.Quotient.field I
  let f := Ideal.Quotient.mk I
  have cp : (11 : R ⧸ I)=0 := by
    simpa only [map_ofNat] using (p.map f).eq_zero
  have strict : ERK (A.map f) := by
    intro i j hij
    change f (A i j)=0
    rw [ha hij,map_zero]
  exact stages_at_least_eleven_field cp strict (HasOrder.map ho f)

theorem exact_order_eight_exists_iff (p : IsNilpotent (11:R)) (s : ℕ) :
    (∃ A : Matrix (Fin s) (Fin s) R, ∃ b : Fin s→R,
      ERK A ∧ HasOrder 8 A b ∧ ¬ HasOrder 9 A b) ↔
      11≤s ∧ IsUnit (Nat.factorial 8:R) := by
  refine ⟨?_,?_⟩
  · rintro ⟨A,b,ha,ho,_⟩
    have t := ho (tallTree 8) (by decide)
    have e : ((tallTree 8).factorial:R)=(Nat.factorial 8:R) := by norm_cast
    exact ⟨stages_at_least_eleven_of_nilpotent p ha ho,IsUnit.of_mul_eq_one _ (e ▸ t)⟩
  · rintro ⟨h,isUnit8⟩
    obtain ⟨A,b,ha,ho,fail⟩ := ERK8FactorialEleven.exists_exact_order_eight isUnit8
    exact ⟨zeroPadMatrix A s,zeroPadVec b s,(zeroPadMatrix_strict_iff h).mpr ha,
      (hasOrder_zeroPad_iff h).mpr ho,fun h9=>fail ((hasOrder_zeroPad_iff h).mp h9)⟩

end RKResearch.Certified.ERK8CharElevenFloor

#print axioms RKResearch.Certified.ERK8CharElevenFloor.no_order8_fin10
#print axioms RKResearch.Certified.ERK8CharElevenFloor.stages_at_least_eleven_of_nilpotent
#print axioms RKResearch.Certified.ERK8CharElevenFloor.exact_order_eight_exists_iff
