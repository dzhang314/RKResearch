/-! Ring gates for the ten-active singleton chart and its primitive cuts. -/
namespace RKResearch.ERK11TenActiveMomentGate
open Lean.Grind
variable {R : Type} [CommRing R]

theorem markedRankOne
    (m₀ m₁ m₂ m₃ z : R)
    (h1 : m₁=z*m₀) (h2 : m₂=z*m₁) (h3 : m₃=z*m₂) :
    m₀*m₂-m₁^2=0 ∧ m₀*m₃-m₁*m₂=0 ∧ m₁*m₃-m₂^2=0 := by
  rw [h3,h2,h1]
  grind

/-- Replace a scalar profile by its edge-kernel numerator without
thereby canceling the edge pivot in a general ring. -/
theorem edgeNumerator
    (l₀ l₁ u v a b : R) (h : l₀*u+l₁*v=0) :
    l₁*(u*a+v*b)=u*(l₁*a-l₀*b) := by
  have e : l₁*v= -(l₀*u) := by grind
  calc
    l₁*(u*a+v*b) = u*l₁*a+(l₁*v)*b := by grind
    _ = u*(l₁*a-l₀*b) := by rw [e]; grind

/-- All four measurements share one literal supporting row.
No response or weight is canceled. -/
theorem fourPrimitivePayments
    (b l r p q m₁ m₂ j g : R)
    (h₁ : m₁=b*p*r) (h₂ : m₂=b*l*q)
    (h₃ : j=b*p*q) (h₄ : g=b*l*r) :
    m₁*m₂=j*g := by
  rw [h₁,h₂,h₃,h₄]
  grind

/-- Coefficient determinant of three homogeneous quadratic marks. -/
theorem quadraticRowsDet
    (a b c d e f g h i z : R)
    (h1 : a+b*z+c*z^2=0) (h2 : d+e*z+f*z^2=0)
    (h3 : g+h*z+i*z^2=0) :
    a*(e*i-f*h)-b*(d*i-f*g)+c*(d*h-e*g)=0 := by
  have ea : a= -(b*z+c*z^2) := by grind
  have ed : d= -(e*z+f*z^2) := by grind
  have eg : g= -(h*z+i*z^2) := by grind
  rw [ea,ed,eg]
  grind

/-- The pair resultant mark remains necessary even if a quadratic
coefficient vanishes. -/
theorem quadraticPairMark
    (a b c d e f z : R)
    (h1 : a+b*z+c*z^2=0) (h2 : d+e*z+f*z^2=0) :
    (a*f-c*d)^2-(a*e-b*d)*(b*f-c*e)=0 := by
  have ea : a= -(b*z+c*z^2) := by grind
  have ed : d= -(e*z+f*z^2) := by grind
  rw [ea,ed]
  grind

end RKResearch.ERK11TenActiveMomentGate
#print axioms RKResearch.ERK11TenActiveMomentGate.markedRankOne
#print axioms RKResearch.ERK11TenActiveMomentGate.edgeNumerator
#print axioms RKResearch.ERK11TenActiveMomentGate.fourPrimitivePayments
#print axioms RKResearch.ERK11TenActiveMomentGate.quadraticRowsDet
#print axioms RKResearch.ERK11TenActiveMomentGate.quadraticPairMark
