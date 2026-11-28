/-! Scalar parts of the physical-edge dormant and repeated-exclusive
mixed contacts. The literal support and the order payments are separate. -/
namespace RKResearch.ERK11EdgeDormantBilinearGate
open Lean.Grind

variable {K : Type} [CommRing K]

theorem edgeDormantRead
    (b z x y Va Vb Q I M : K)
    (hI : I=b*(z-x)*(z-y)*Va*Vb)
    (hM : M=b*(z-x)*Va*Q) :
    I*Q=M*(z-y)*Vb := by
  rw [hI,hM]
  grind

theorem innerPrimitiveMark
    (b s x z V D A P Q M J : K)
    (hM : M=b*(x-z)*(s*V)*Q)
    (hJ : J=b*P*Q)
    (hContact : s*D+30*P*A=0) :
    M*D+30*V*(x-z)*J*A=0 := by
  have hp : M*D+30*V*(x-z)*J*A =
      b*(x-z)*V*Q*(s*D+30*P*A) := by
    rw [hM,hJ]
    grind
  rw [hp,hContact]
  grind

theorem cubicDividedDifference
    (w z c0 c1 c2 c3 d0 d1 d2 d3 : K) :
    ((c0+c1*w+c2*w^2+c3*w^3)*(d0+d1*z+d2*z^2+d3*z^3)
      -(d0+d1*w+d2*w^2+d3*w^3)*(c0+c1*z+c2*z^2+c3*z^3)) =
    (w-z)*
      ((c1+c2*(w+z)+c3*(w^2+w*z+z^2))*(d0+d1*z+d2*z^2+d3*z^3)
        -(d1+d2*(w+z)+d3*(w^2+w*z+z^2))*(c0+c1*z+c2*z^2+c3*z^3)) := by
  grind

end RKResearch.ERK11EdgeDormantBilinearGate

#print axioms RKResearch.ERK11EdgeDormantBilinearGate.edgeDormantRead
#print axioms RKResearch.ERK11EdgeDormantBilinearGate.innerPrimitiveMark
#print axioms RKResearch.ERK11EdgeDormantBilinearGate.cubicDividedDifference
