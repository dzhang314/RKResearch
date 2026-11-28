/-! Division-free cubic-remainder determinant and scaled quadratic norms. -/
namespace RKResearch.ERK11CubicRemainderNormGate
open Lean.Grind
variable {R : Type} [CommRing R]

theorem cubicResidueDeterminant
    (s m a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : R) :
    (a₀-a₂*m-a₃*s*m)*(b₁+b₂*s+b₃*(s^2-m)) -
      (a₁+a₂*s+a₃*(s^2-m))*(b₀-b₂*m-b₃*s*m) =
      m^2*(a₂*b₃-a₃*b₂) + m*s*(a₁*b₃-a₃*b₁) +
      m*(-a₀*b₃+a₁*b₂-a₂*b₁+a₃*b₀) +
      s^2*(a₀*b₃-a₃*b₀) + s*(a₀*b₂-a₂*b₀) + (a₀*b₁-a₁*b₀) := by
  grind

theorem scaledQuadraticNorm
    (d s p u v z : R)
    (hQ : d*z^2-s*z+p=0) (hA : u*z+v=0) :
    d*v^2+s*u*v+p*u^2=0 := by
  have e : v= -(u*z) := by grind
  rw [e]
  calc
    d*(-(u*z))^2 + s*u*(-(u*z)) + p*u^2 =
        u^2*(d*z^2-s*z+p) := by grind
    _ = 0 := by rw [hQ]; grind

theorem centeredNormBeforeCancellation
    (d s p u v z : R)
    (hQ : d*z^2-s*z+p=0) (hA : d*u*z+v=0) :
    d*(v^2+s*u*v+p*d*u^2)=0 := by
  have h := scaledQuadraticNorm d s p (d*u) v z hQ hA
  calc
    d*(v^2+s*u*v+p*d*u^2) =
        d*v^2+s*(d*u)*v+p*(d*u)^2 := by grind
    _ = 0 := h

end RKResearch.ERK11CubicRemainderNormGate
#print axioms RKResearch.ERK11CubicRemainderNormGate.cubicResidueDeterminant
#print axioms RKResearch.ERK11CubicRemainderNormGate.scaledQuadraticNorm
#print axioms RKResearch.ERK11CubicRemainderNormGate.centeredNormBeforeCancellation
