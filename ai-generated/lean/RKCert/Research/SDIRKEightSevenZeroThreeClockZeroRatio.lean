import Mathlib.Tactic.Ring.Basic

/-!
Clear the actual terminal duplicate correction and verify the zero-ratio
first-clock cubic comparison. These are not rooted tableau theorems.
-/

namespace RKResearch.Certified.SDIRKEightSevenZeroThreeClockZeroRatio

variable {R : Type*} [CommRing R]

/-- Cancel the terminal physical donor by a pure pair difference. At the
early occurrence the surviving weight is the whole ordinary clock aggregate. -/
theorem terminal_pair_adjustment {b₀ b₁ p a z₀ z₁ : R}
    (hz : z₀+z₁=0) (ht : b₁*p-a*z₁=0) :
    b₀*p-a*z₀=(b₀+b₁)*p := by
  calc
    _ = (b₀+b₁)*p-(b₁*p-a*z₁)-a*(z₀+z₁) := by ring1
    _ = _ := by rw [ht,hz,mul_zero,sub_zero,sub_zero]

/-- The front cubic needed when literal row three is a zero also kills
the first primitive of the star baseline, with denominators cleared. -/
theorem front_first_primitive_cubic (u : R) :
    -(1+2*u)^3+9*(1+2*u)^2-18*(1+2*u)+6 =
      -2*(4*u^3-12*u^2+3*u+2) := by ring1

/-- Compare the cleared aggregate reads at the penultimate and fourth-from-
rear supported occurrences; the same pure multiplier appears on each. -/
theorem equal_barycentric_multiplier {Bₑ Bₜ Rₑ Jₑ Jₜ m : R}
    (he : (Rₑ-Jₑ)*Bₑ=m) (ht : -(Jₜ*Bₜ)=m) :
    (Rₑ-Jₑ)*Bₑ+Jₜ*Bₜ=0 := by
  rw [he,← ht]
  ring1

end RKResearch.Certified.SDIRKEightSevenZeroThreeClockZeroRatio
