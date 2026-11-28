import Mathlib.Tactic.Ring.Basic

/-!
Scalar determinantal receipts for the three-off-clock, five-zero-label
SDIRK8 projection. Neither theorem assumes or proves rooted order.
-/

namespace RKResearch.Certified.SDIRKEightSevenZeroThreeClockFiveLabel

variable {R : Type*} [CommRing R]

def det3 (a b c d e f g h i : R) : R :=
  a*(e*i-f*h)-b*(d*i-f*g)+c*(d*h-e*g)

/-- If a row really has only two contributing supported donors, its
three scalar affine reads have singular augmented matrix. -/
theorem two_supported_donors
    {a b c d e f g h i x y : R}
    (h0 : c=a*x+b*y) (h1 : f=d*x+e*y) (h2 : i=g*x+h*y) :
    det3 a b c d e f g h i = 0 := by
  unfold det3
  rw [h0,h1,h2]
  ring1

/-- The monic two-clock completion forces a Hankel determinant to vanish
independently of whether the lower moment pivot is zero. -/
theorem monic_two_clock_moment_kernel
    {m₀ m₁ m₂ m₃ m₄ q₀ q₁ : R}
    (h0 : m₀*q₀+m₁*q₁+m₂=0) (h1 : m₁*q₀+m₂*q₁+m₃=0)
    (h2 : m₂*q₀+m₃*q₁+m₄=0) :
    det3 m₀ m₁ m₂ m₁ m₂ m₃ m₂ m₃ m₄ = 0 := by
  apply two_supported_donors (x := -q₀) (y := -q₁)
  · calc
      _ = (m₀*q₀+m₁*q₁+m₂) + (m₀*(-q₀)+m₁*(-q₁)) := by ring1
      _ = _ := by rw [h0,zero_add]
  · calc
      _ = (m₁*q₀+m₂*q₁+m₃) + (m₁*(-q₀)+m₂*(-q₁)) := by ring1
      _ = _ := by rw [h1,zero_add]
  · calc
      _ = (m₂*q₀+m₃*q₁+m₄) + (m₂*(-q₀)+m₃*(-q₁)) := by ring1
      _ = _ := by rw [h2,zero_add]

end RKResearch.Certified.SDIRKEightSevenZeroThreeClockFiveLabel
