
/-! Scalar product cancellation behind the paid central repeated-pair
clock equation. Physical supports and order payment are separate. -/
namespace RKResearch.ERK11CentralRepeatedPairProductGate
open Lean.Grind

variable {K : Type} [CommRing K]

theorem centralProduct
    (b z u P Q VL VR H C1 C2 J I : K)
    (h1 : C1-u*H = b*(z-u)*P*VR)
    (h2 : C2-u*H = b*(z-u)*VL*Q)
    (hJ : J = b*P*Q)
    (hI : I = b*(z-u)^2*(VL*VR)) :
    (C1-u*H)*(C2-u*H)=J*I := by
  rw [h1,h2,hJ,hI]
  grind

theorem aliasZero (b u VL VR I : K)
    (hI : I = b*(u-u)^2*(VL*VR)) : I=0 := by
  rw [hI]
  grind

end RKResearch.ERK11CentralRepeatedPairProductGate
#print axioms RKResearch.ERK11CentralRepeatedPairProductGate.centralProduct
#print axioms RKResearch.ERK11CentralRepeatedPairProductGate.aliasZero
