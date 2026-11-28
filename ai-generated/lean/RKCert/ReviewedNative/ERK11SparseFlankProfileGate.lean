/-! Denominator-free scalar transformations of the unordered-extras profile. -/
namespace RKResearch.ERK11SparseFlankProfileGate
open Lean.Grind
variable {R : Type} [CommRing R]

theorem sparseProfile
    (x a h u c a₀ b t b₁ : R) :
    let phi := x^2*(a-x)
    let b₀ := x*(x-a)*(x-h)
    (u+c*(x-h))*phi+(a₀+b*x)*(b₀+t*b₁) =
      u*phi+(b-c)*x*b₀+(t*b)*x*b₁+a₀*(b₀+t*b₁) := by
  dsimp
  grind

theorem sparseOuter
    (x a h u c a₀ b t e s₁ : R) :
    let s₀ := -a*e*(x-a)*(x-h)
    (u+c*(x-h))*a*x*(x-a)*e+(a₀+b*x)*(s₀+t*s₁) =
      u*a*x*(x-a)*e+(b-c)*x*s₀+(t*b)*x*s₁+a₀*(s₀+t*s₁) := by
  dsimp
  grind

theorem scaleFirstPool (p₀ p₁ u w z t h : R)
    (hu : u=p₀+h*p₁)
    (ht : z=t*(w+p₁)) :
    z-t*w=t*p₁ ∧ t*u-h*(z-t*w)=t*p₀ := by
  rw [hu,ht]
  grind

theorem reflectedPoolProjectivity
    (p₀ p₁ r₀ r₁ q : R)
    (h0 : p₀=q*(r₀+r₁)) (h1 : p₁=q*(-r₁)) :
    p₀*r₁+p₁*(r₀+r₁)=0 := by
  rw [h0,h1]
  grind

end RKResearch.ERK11SparseFlankProfileGate
#print axioms RKResearch.ERK11SparseFlankProfileGate.sparseProfile
#print axioms RKResearch.ERK11SparseFlankProfileGate.sparseOuter
#print axioms RKResearch.ERK11SparseFlankProfileGate.scaleFirstPool
#print axioms RKResearch.ERK11SparseFlankProfileGate.reflectedPoolProjectivity
