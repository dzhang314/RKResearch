/-! Scalar division-free gates for the switched-plateau mixed primitive proof. -/
namespace RKResearch.ERK11SwitchedPlateauPrimitiveGate
open Lean.Grind
variable {R : Type} [CommRing R]

/-- Apply the response cubic hull to a local functional whose moments
factor through a mass at zero and a mass at the pooled profile. -/
theorem plateauResponseHull
    (b₁ b₂ b₃ p e u l n k : R)
    (h0 : b₁+b₂+b₃ = l+n)
    (h1 : b₁*p+b₂*e+b₃*u = n*k)
    (h2 : b₁*p^2+b₂*e^2+b₃*u^2 = n*k^2)
    (h3 : b₁*p^3+b₂*e^3+b₃*u^3 = n*k^3) :
    l*p*e*u = n*(k-p)*(k-e)*(k-u) := by
  have h :
      (b₁*p^3+b₂*e^3+b₃*u^3)
       -(p+e+u)*(b₁*p^2+b₂*e^2+b₃*u^2)
       +(p*e+p*u+e*u)*(b₁*p+b₂*e+b₃*u)
       -p*e*u*(b₁+b₂+b₃) = 0 := by grind
  rw [h0,h1,h2,h3] at h
  have e₀ :
      n*k^3-(p+e+u)*(n*k^2)+(p*e+p*u+e*u)*(n*k)-p*e*u*(l+n) =
        n*(k-p)*(k-e)*(k-u)-l*p*e*u := by grind
  rw [e₀] at h
  grind

/-- Test the deviation charges by the Lagrange numerator of the actual
foreign response, without reciprocal response hypotheses. -/
theorem foreignDeviation
    (s₁ s₂ s₃ p e u t : R)
    (h0 : s₁+s₂+s₃=t)
    (h1 : p*s₁+e*s₂+u*s₃=0)
    (h2 : p^2*s₁+e^2*s₂+u^2*s₃=0) :
    (e-p)*(e-u)*s₂ = p*u*t := by
  calc
    (e-p)*(e-u)*s₂ =
        (p^2*s₁+e^2*s₂+u^2*s₃)
        -(p+u)*(p*s₁+e*s₂+u*s₃)+p*u*(s₁+s₂+s₃) := by grind
    _ = p*u*t := by rw [h0,h1,h2]; grind

/-- The product of the two oriented outer-clock marks depends on
only the sum and product of that unordered pair. -/
theorem oppositePairProduct
    (a b c d x z : R) :
    (a*x*z+b*x+c*z+d)*(a*z*x+b*z+c*x+d) =
      (a*(x*z)+d)^2+(b+c)*(a*(x*z)+d)*(x+z)+b*c*(x+z)^2+(b-c)^2*(x*z) := by
  grind

/-- After two divided-difference functionals kill the quadratic mode. -/
theorem eliminateSharedMode
    (g u₀ u₁ v₀ v₁ : R)
    (h0 : u₀=g*v₀) (h1 : u₁=g*v₁) :
    u₀*v₁-u₁*v₀=0 := by
  rw [h0,h1]
  grind

end RKResearch.ERK11SwitchedPlateauPrimitiveGate
#print axioms RKResearch.ERK11SwitchedPlateauPrimitiveGate.plateauResponseHull
#print axioms RKResearch.ERK11SwitchedPlateauPrimitiveGate.foreignDeviation
#print axioms RKResearch.ERK11SwitchedPlateauPrimitiveGate.oppositePairProduct
#print axioms RKResearch.ERK11SwitchedPlateauPrimitiveGate.eliminateSharedMode
