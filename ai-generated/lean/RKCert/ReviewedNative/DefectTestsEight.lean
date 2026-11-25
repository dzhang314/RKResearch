module

public import RKCert.ReviewedNative.DefectLowGrades

import Mathlib.Tactic.IntervalCases

@[expose] public section

/-! # A sufficient native order-eight certificate on genuine low defects -/
namespace RKResearch.Certified.Graded

open LowDefects

variable {ι R : Type*} [Fintype ι] [CommRing R]

/-- The actual grade-six and grade-seven products are explicit. No
common diagonal, seed support, or characteristic-zero hypothesis occurs. -/
structure DefectTestsEight (B : Matrix ι ι R) (b : ι → R) (z : R)
    (U : Submodule R (ι → R)) : Prop where
  cover : CubicCover B U
  quadrature : ScaledClockMoments B b z 8
  adjoint : ScaledD1 B b z
  seed_silent : seedSpace B ≤ probeCut B b 5
  cubic_silent : U ≤ probeCut B b 4
  quartic_silent : quartic B U ≤ probeCut B b 3
  quintic_silent : quintic B U ≤ probeCut B b 2
  advance_quintic : quintic B U ≤ (probeCut B b 1).comap (mat B)
  primitive_six : monomialStageDefect B 5 ∈ probeCut B b 1
  seed_quartic : ProductsIn (seedSpace B) (quartic B U) (probeCut B b 1)
  cubic_square : ProductsIn U U (probeCut B b 1)
  seed_quintic : ProductsIn (seedSpace B) (quintic B U) (probeCut B b 0)
  cubic_quartic : ProductsIn U (quartic B U) (probeCut B b 0)

namespace DefectTestsEight

variable {B : Matrix ι ι R} {b : ι → R} {z : R} {U : Submodule R (ι → R)}

theorem tail (h : DefectTestsEight B b z U) :
    DefectTailTwo (prefixQuintic h.cover) b z where
  quadrature := h.quadrature
  adjoint := h.adjoint
  prefix_silent := by
    intro j hj
    interval_cases j
    · exact bot_le
    · exact bot_le
    · exact h.seed_silent.trans (probeCut_anti B b (by decide : 0 ≤ 5))
    · exact h.cubic_silent.trans (probeCut_anti B b (by decide : 0 ≤ 4))
    · exact h.quartic_silent.trans (probeCut_anti B b (by decide : 0 ≤ 3))
    · exact h.quintic_silent.trans (probeCut_anti B b (by decide : 0 ≤ 2))
  last_two := h.quintic_silent
  advance_last := h.advance_quintic
  primitive_last := h.primitive_six
  product_one := by
    intro j k hj hk hsum
    have e : (j = 2 ∧ k = 4) ∨ (j = 3 ∧ k = 3) ∨ (j = 4 ∧ k = 2) := by omega
    rcases e with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h.seed_quartic
    · exact h.cubic_square
    · exact h.seed_quartic.swap
  product_zero := by
    intro j k hj hk hsum
    have e : (j = 2 ∧ k = 5) ∨ (j = 3 ∧ k = 4) ∨
        (j = 4 ∧ k = 3) ∨ (j = 5 ∧ k = 2) := by omega
    rcases e with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h.seed_quintic
    · exact h.cubic_quartic
    · exact h.cubic_quartic.swap
    · exact h.seed_quintic.swap

/-- The actual reviewed order of the original tableau. -/
theorem hasOrder_of_scale {A : Matrix ι ι R} (hz : IsLeftRegular z)
    (h : DefectTestsEight (z • A) b z U) : RKResearch.HasOrder 8 A b :=
  h.tail.hasOrder_of_scale (by decide) hz

theorem hasOrder_of_unit_scale {A : Matrix ι ι R} (hz : IsUnit z)
    (h : DefectTestsEight (z • A) b z U) : RKResearch.HasOrder 8 A b :=
  hasOrder_of_scale hz.isRegular.left h

end DefectTestsEight
end RKResearch.Certified.Graded
