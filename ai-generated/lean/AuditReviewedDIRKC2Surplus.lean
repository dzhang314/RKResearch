import RKCert.ReviewedNative.DIRKC2StageJoin
import Mathlib.Data.ZMod.Basic

open RKResearch RKResearch.Certified.Graded
open scoped Matrix

#print axioms OuterHead.c2_core_mask
#print axioms OuterHead.outsideSites_card
#print axioms OuterHead.clockDebuts_of_card
#print axioms OuterHead.early_exterior_head
#print axioms OuterHead.exterior_refund
#print axioms OuterHead.ExteriorStep.fit_full_prefix
#print axioms OuterHead.ExteriorStep.paired_cut
#print axioms OuterHead.barycentric_native
#print axioms OuterHead.no_grade_four_exterior_head
#print axioms dirk_grade_six_surplus_C2
#print axioms monomialStageDefect_map
#print axioms HasOrder.dirk_C2_stage_floor_field
#print axioms HasOrder.dirk_C2_stage_floor
#print axioms RKCert.FourDebut.fourth_impossible

example {K : Type*} [Field K] [CharZero K] {s : ℕ}
    {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
    (order : HasOrder 8 A b) (ha : A.IsLowerTriangular) (c₂ : monomialStageDefect A 1=0) :
    Module.finrank K (zeroSpace A 3)+4 ≤ Module.finrank K (zeroSpace A 6) :=
  dirk_grade_six_surplus_C2 ha order (by decide) c₂

section
local instance : CharZero (ℚ × ZMod 529) :=
  ⟨fun _ _ h => Nat.cast_injective (R:=ℚ) (congrArg Prod.fst h)⟩

example {s : ℕ} {A : Matrix (Fin s) (Fin s) (ℚ × ZMod 529)} {b : Fin s → (ℚ × ZMod 529)}
    (order : HasOrder 12 A b) (ha : A.IsLowerTriangular) (c₂ : monomialStageDefect A 1=0) : 15≤s :=
  order.dirk_C2_stage_floor ha (by decide) c₂
end

example {R : Type*} [CommRing R] [CharZero R] {s : ℕ} {A : Matrix (Fin s) (Fin s) R} {b : Fin s → R}
    (order : HasOrder 13 A b) (ha : A.IsLowerTriangular) (c₂ : monomialStageDefect A 1=0) : 17≤s :=
  order.dirk_C2_stage_floor ha (by decide) c₂

example {R : Type*} [CommRing R] [CharZero R] {s : ℕ} {A : Matrix (Fin s) (Fin s) R} {b : Fin s → R}
    (order : HasOrder 15 A b) (ha : A.IsLowerTriangular) (c₂ : monomialStageDefect A 1=0) : 20≤s :=
  order.dirk_C2_stage_floor ha (by decide) c₂
