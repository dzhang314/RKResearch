module

public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8NonliteralFifth

/-- The actual fifth's virtual cubic amplitude can be zero. Eliminating
it divides by the active fourth's amplitude only. -/
theorem eliminateFifthAmplitude
    {K : Type*} [Field K] (h₄ h₅ t₀ t₁ a₀ a₁ : K) (hh : h₄ ≠ 0)
    (ht : h₄ * t₀ + t₁ * h₅ = 0)
    (ha : h₄ * a₀ + a₁ * h₅ = 0) :
    t₀ * a₁ - a₀ * t₁ = 0 := by
  have h : h₄ * (t₀ * a₁ - a₀ * t₁) = 0 := by
    linear_combination a₁ * ht - t₁ * ha
  exact (mul_eq_zero.mp h).resolve_left hh

/-- The ninth reverse equation fixes the affine transport coordinate.
The protected nonzero quantity is the actual trailing numerator, not
the fifth's amplitude or the value of (L_4) at the fifth. -/
theorem ninthAffineTransport
    {K : Type*} [Field K] (γ x y a b : K) (hb : b ≠ 0)
    (h : a * (x - γ * y) + b = 0) :
    a ≠ 0 ∧ γ * a * y = x * a + b := by
  have ha : a ≠ 0 := by
    intro ha
    have h' : b = 0 := by simpa [ha] using h
    exact hb h'
  refine ⟨ha, ?_⟩
  linear_combination -h

/-- The cubic chronological replacement remains exact when the physical
fourth shares a clock with a literal silent. No interpolation division
by a node difference is used. -/
theorem cubicReadWithRepeatedClock
    {R : Type*} [CommRing R] (a b s u v w : R) :
    u * a^3 + v * b^3 + w * s^3 =
      (a + b + s) * (u * a^2 + v * b^2 + w * s^2) -
      (a*b + a*s + b*s) * (u*a + v*b + w*s) +
      a*b*s * (u+v+w) := by
  ring

end RKCert.ReviewedNative.SDIRK8NonliteralFifth

#print axioms RKCert.ReviewedNative.SDIRK8NonliteralFifth.eliminateFifthAmplitude
#print axioms RKCert.ReviewedNative.SDIRK8NonliteralFifth.ninthAffineTransport
#print axioms RKCert.ReviewedNative.SDIRK8NonliteralFifth.cubicReadWithRepeatedClock
