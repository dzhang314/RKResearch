module

public import RKCert.ReviewedNative.DefectLowGrades

import Mathlib.Tactic.IntervalCases

@[expose] public section

/-! # A sufficient native order-seven certificate on genuine low defects -/
namespace RKResearch.Certified.Graded

open LowDefects

variable {ι R : Type*} [Fintype ι] [CommRing R]

/-- The submodule interface behind the order-seven test table.
The cubic cover U can be generated, or supplied by a smaller rank chart.
There is no support, diagonal, or characteristic hypothesis. -/
structure DefectTestsSeven (B : Matrix ι ι R) (b : ι → R) (z : R)
    (U : Submodule R (ι → R)) : Prop where
  cover : CubicCover B U
  quadrature : ScaledClockMoments B b z 7
  adjoint : ScaledD1 B b z
  seed_silent : seedSpace B ≤ probeCut B b 4
  cubic_silent : U ≤ probeCut B b 3
  quartic_silent : quartic B U ≤ probeCut B b 2
  quintic_silent : quintic B U ≤ probeCut B b 1
  seed_quartic : ProductsIn (seedSpace B) (quartic B U) (probeCut B b 0)
  cubic_square : ProductsIn U U (probeCut B b 0)

namespace DefectTestsSeven

variable {B : Matrix ι ι R} {b : ι → R} {z : R} {U : Submodule R (ι → R)}

theorem tail (h : DefectTestsSeven B b z U) :
    DefectTailTwo (prefixQuartic h.cover) b z where
  quadrature := h.quadrature
  adjoint := h.adjoint
  prefix_silent := by
    intro j hj
    interval_cases j
    · exact bot_le
    · exact bot_le
    · exact h.seed_silent.trans (probeCut_anti B b (by decide : 0 ≤ 4))
    · exact h.cubic_silent.trans (probeCut_anti B b (by decide : 0 ≤ 3))
    · exact h.quartic_silent.trans (probeCut_anti B b (by decide : 0 ≤ 2))
  last_two := h.quartic_silent
  advance_last := ((quintic_le_iff B U _).mp h.quintic_silent).2.2.1
  primitive_last := ((quintic_le_iff B U _).mp h.quintic_silent).2.2.2.2
  product_one := by
    intro j k hj hk hsum
    have hp := (quintic_seed_product (B := B) (U := U)).mono h.quintic_silent
    have e : (j = 2 ∧ k = 3) ∨ (j = 3 ∧ k = 2) := by omega
    rcases e with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hp
    · exact hp.swap
  product_zero := by
    intro j k hj hk hsum
    have e : (j = 2 ∧ k = 4) ∨ (j = 3 ∧ k = 3) ∨ (j = 4 ∧ k = 2) := by omega
    rcases e with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h.seed_quartic
    · exact h.cubic_square
    · exact h.seed_quartic.swap

/-- The actual reviewed order of the original, unscaled tableau.
Only the chosen homogeneous scale is canceled. -/
theorem hasOrder_of_scale {A : Matrix ι ι R} (hz : IsLeftRegular z)
    (h : DefectTestsSeven (z • A) b z U) : RKResearch.HasOrder 7 A b :=
  h.tail.hasOrder_of_scale (by decide) hz

theorem hasOrder_of_unit_scale {A : Matrix ι ι R} (hz : IsUnit z)
    (h : DefectTestsSeven (z • A) b z U) : RKResearch.HasOrder 7 A b :=
  hasOrder_of_scale hz.isRegular.left h

end DefectTestsSeven
end RKResearch.Certified.Graded
