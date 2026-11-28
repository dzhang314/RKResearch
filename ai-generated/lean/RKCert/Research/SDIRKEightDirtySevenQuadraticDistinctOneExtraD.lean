import Mathlib.Tactic.Ring.Basic

namespace RKResearch.Certified.SDIRKEightDirtySevenQuadraticDistinctOneExtraD

variable {R : Type*} [CommRing R]

theorem simultaneous_affine_d_fibre {a₀ a₁ b₀ b₁ d : R}
    (ha : a₀+a₁*d=0) (hb : b₀+b₁*d=0) : a₀*b₁-a₁*b₀=0 := by
  calc
    _ = (a₀+a₁*d)*b₁-a₁*(b₀+b₁*d) := by ring1
    _ = 0 := by rw [ha, hb]; ring1

end RKResearch.Certified.SDIRKEightDirtySevenQuadraticDistinctOneExtraD
