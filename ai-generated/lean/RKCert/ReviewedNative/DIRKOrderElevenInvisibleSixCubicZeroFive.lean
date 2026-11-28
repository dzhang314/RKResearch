module

public import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Scalar cores of the cubic zero-multiplier five-prefix cut -/
namespace RKResearch.Certified.Graded.OrderElevenInvisibleSixCubicZeroFive

section Ring
variable {K : Type*} [CommRing K]

def det₃ (a b c d e f g h i : K) : K :=
  a*(e*i-f*h)-b*(d*i-f*g)+c*(d*h-e*g)

def adj0 (V c₀ c₁ c₂ : K) : K :=
  -V^2*(9*V^3+15*V^2*c₂+25*V*c₁+45*c₀)
def adj1 (V c₀ c₁ c₂ : K) : K :=
  V*(24*V^3+45*V^2*c₂+80*V*c₁+150*c₀)
def adj2 (V c₀ c₁ c₂ : K) : K :=
  -5*(2*V^3+5*V^2*c₂+10*V*c₁+20*c₀)
def lread (V c₀ c₁ c₂ : K) : K := 12*V^3+15*V^2*c₂+20*V*c₁+30*c₀
def normD (V c₀ c₁ c₂ : K) : K :=
  27*V^6+90*V^5*c₂+165*V^4*c₁+75*V^4*c₂^2+
  325*V^3*c₀+275*V^3*c₁*c₂+550*V^2*c₀*c₂+
  250*V^2*c₁^2+1000*V*c₀*c₁+1000*c₀^2

set_option maxHeartbeats 2500000 in
/-- The universal affine-mark determinant after scaling its
third column by 12. No field-specific arithmetic is needed. -/
theorem affine_determinant (V c₀ c₁ c₂ : K) :
    let a := adj0 V c₀ c₁ c₂
    let b := adj1 V c₀ c₁ c₂
    let c := adj2 V c₀ c₁ c₂
    det₃ a (-c₀*c) (-3*c₀*c)
      b (a-c₁*c) (6*a-3*c₁*c)
      c (b-c₂*c) (4*b-3*c₂*c) =
      -V^2 * (lread V c₀ c₁ c₂)^2 * normD V c₀ c₁ c₂ := by
  simp only [adj0,adj1,adj2,det₃,lread,normD]
  ring

/-- The initial-ghost hull condition in its division-free
three-coefficient form. -/
theorem mixed_prefix_gate (f₀ f₁ f₂ g₀ g₁ g₂ d₀ d₁ d₂ z ell : K)
    (h₀ : g₀=z*f₀+ell*d₀) (h₁ : g₁=z*f₁+ell*d₁) (h₂ : g₂=z*f₂+ell*d₂) :
    det₃ f₀ g₀ d₀ f₁ g₁ d₁ f₂ g₂ d₂ = 0 := by
  rw [h₀,h₁,h₂,det₃]
  ring
end Ring

end RKResearch.Certified.Graded.OrderElevenInvisibleSixCubicZeroFive
