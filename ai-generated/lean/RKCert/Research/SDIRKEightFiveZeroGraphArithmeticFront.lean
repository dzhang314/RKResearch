import Mathlib.Tactic.Ring.Basic

/-!
Division-free graph-pencil eliminants for the arithmetic opening of the
ten-row, five literal quadratic-zero SDIRK order-eight boundary.
These statements only check ring1 algebra after the scalar ingress.
-/

namespace RKResearch.Certified.SDIRKEightFiveZeroGraphArithmeticFront

variable {R : Type*} [CommRing R]

def gapCubic (u : R) : R := -2 + u + 4 * u^2 - u^3

def arithEliminant (a b d : R) : R :=
  -2*a^3 - b*a^2 + 4*b^2*a + b^3 + (3*b*a + 2*a^2)*d

/-- The first two zero-row gates give the pencil numerators by Cramer, without
requiring or assuming a nonzero determinant. -/
theorem pencil_cramer {f₀ f₁ f₂ g₀ g₁ g₂ a b : R}
    (hf : f₀ + f₁*b + f₂*a = 0) (hg : g₀ + g₁*b + g₂*a = 0) :
    let Δ := f₁*g₂ - f₂*g₁
    a*Δ = f₀*g₁ - f₁*g₀ ∧ b*Δ = f₂*g₀ - f₀*g₂ := by
  dsimp
  constructor
  · calc
      _ = (f₀*g₁ - f₁*g₀) + f₁*(g₀+g₁*b+g₂*a) - g₁*(f₀+f₁*b+f₂*a) := by ring1
      _ = _ := by rw [hf, hg]; ring1
  · calc
      _ = (f₂*g₀ - f₀*g₂) + g₂*(f₀+f₁*b+f₂*a) - f₂*(g₀+g₁*b+g₂*a) := by ring1
      _ = _ := by rw [hf, hg]; ring1

/-- A third supported read, in the same linear pencil, gives its determinant
eliminant whether or not the first two equations are independent. -/
theorem pencil_third_gate {h₀ h₁ h₂ a b aₙ bₙ Δ : R}
    (hh : h₀ + h₁*b + h₂*a = 0) (ha : a*Δ = aₙ) (hb : b*Δ = bₙ) :
    Δ*h₀ + bₙ*h₁ + aₙ*h₂ = 0 := by
  calc
    _ = Δ*(h₀+h₁*b+h₂*a) - h₂*(a*Δ-aₙ) - h₁*(b*Δ-bₙ) := by ring1
    _ = _ := by rw [hh,ha,hb]; ring1

/-- The literal arithmetic third establishes the cubic relation in the graph
parameter. Clearing Cramer's determinant introduces no new hypotheses. -/
theorem pencil_arithmetic_gate {u a b aₙ bₙ Δ : R}
    (hgap : a * gapCubic u = 3*u - 2) (hb0 : b = -u*a)
    (ha : a*Δ = aₙ) (hb : b*Δ = bₙ) :
    arithEliminant aₙ bₙ Δ = 0 := by
  rw [← ha, ← hb, hb0]
  calc
    _ = (a^2*Δ^3)*(a*gapCubic u-(3*u-2)) := by unfold arithEliminant gapCubic; ring1
    _ = _ := by rw [hgap,sub_self,mul_zero]

/-- A singular Cramer pencil has both numerators zero; it cannot disappear
from a guarded eliminant based on division. -/
theorem pencil_singular {f₀ f₁ f₂ g₀ g₁ g₂ a b : R}
    (hf : f₀ + f₁*b + f₂*a = 0) (hg : g₀ + g₁*b + g₂*a = 0)
    (hΔ : f₁*g₂ - f₂*g₁ = 0) :
    f₀*g₁ - f₁*g₀ = 0 ∧ f₂*g₀ - f₀*g₂ = 0 := by
  have h := pencil_cramer hf hg
  dsimp at h
  rw [hΔ, mul_zero, mul_zero] at h
  exact ⟨h.1.symm,h.2.symm⟩

end RKResearch.Certified.SDIRKEightFiveZeroGraphArithmeticFront
