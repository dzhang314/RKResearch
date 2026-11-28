module

public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8NonliteralFourth

open Polynomial

/-- Two reflected star rears give both centered affine reads at the
same squared gap. Neither coefficient of the affine reads is assumed to be a unit. -/
theorem reflectedAffineEvenOdd
    {K : Type*} [Field K] (h₂ : (2 : K) ≠ 0)
    (v a₀ a₁ b₀ b₁ : K) (hv : v ≠ 0)
    (hp : a₀ + a₁ * v^2 + v * (b₀ + b₁ * v^2) = 0)
    (hm : a₀ + a₁ * v^2 - v * (b₀ + b₁ * v^2) = 0) :
    a₀ + a₁ * v^2 = 0 ∧ b₀ + b₁ * v^2 = 0 := by
  have ha : 2 * (a₀ + a₁ * v^2) = 0 := by linear_combination hp + hm
  have hb : (2 * v) * (b₀ + b₁ * v^2) = 0 := by linear_combination hp - hm
  exact ⟨(mul_eq_zero.mp ha).resolve_left h₂,
    (mul_eq_zero.mp hb).resolve_left (mul_ne_zero h₂ hv)⟩

/-- For an actual translated extra reverse clock, the raw penultimate
cross cannot be identically zero in the clock: test it at that extra clock. -/
theorem ninthCrossNonzero
    {K : Type*} [Field K] (qₓ x z : K) (L P : K[X])
    (hq : qₓ ≠ 0) (hz : x - z ≠ 0) (hL : L.eval z ≠ 0) :
    C (qₓ * (x - z)) * L - P * (X - C z) ≠ 0 := by
  intro h
  have e := congrArg (fun F : K[X] => F.eval z) h
  simp at e
  rcases e with (e | e) | e
  · exact hq e
  · exact hz e
  · exact hL e

end RKCert.ReviewedNative.SDIRK8NonliteralFourth

#print axioms RKCert.ReviewedNative.SDIRK8NonliteralFourth.reflectedAffineEvenOdd
#print axioms RKCert.ReviewedNative.SDIRK8NonliteralFourth.ninthCrossNonzero
