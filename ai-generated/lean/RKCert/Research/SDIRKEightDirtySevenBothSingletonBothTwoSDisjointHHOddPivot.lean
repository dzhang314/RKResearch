import Mathlib.Tactic.Ring.Basic

/-! Scalar gates for the odd singleton-quartic pivot. -/
namespace RKCert.Research.SDIRKEightDirtySevenBothSingletonBothTwoSDisjointHHOddPivot

theorem odd_nodal_pivot_zero {R : Type*} [CommRing R]
    (delta U V r₁ r₂ L c₂ : R)
    (h₀ : r₁ + delta * r₂ = 0)
    (h₃ : r₁ * (c₂ - 4 * L * r₂) = delta * (U * V - r₂ * c₂)) :
    delta * (U * V - 4 * L * r₂ ^ 2) = 0 := by
  have hw : r₁ = -(delta * r₂) := by
    calc
      r₁ = (r₁ + delta * r₂) - delta * r₂ := by ring1
      _ = -(delta * r₂) := by rw [h₀, zero_sub]
  calc
    delta * (U * V - 4 * L * r₂ ^ 2) =
        delta * (U * V - r₂ * c₂) - r₁ * (c₂ - 4 * L * r₂) := by rw [hw]; ring1
    _ = 0 := sub_eq_zero.mpr h₃.symm

theorem cubic_special_shape {R : Type*} [CommRing R]
    (a b r₀ r₂ delta m₀ m₁ m₂ m₃ : R)
    (h₀ : m₀ = a * r₀) (h₁ : m₁ = b * r₀ - a * delta * r₂)
    (h₂ : m₂ = a * r₂ - b * delta * r₂) (h₃ : m₃ = b * r₂) :
    m₀ * m₃ = (m₂ + delta * m₃) * (m₁ + delta * (m₂ + delta * m₃)) := by
  rw [h₀, h₁, h₂, h₃]
  ring1

end RKCert.Research.SDIRKEightDirtySevenBothSingletonBothTwoSDisjointHHOddPivot
