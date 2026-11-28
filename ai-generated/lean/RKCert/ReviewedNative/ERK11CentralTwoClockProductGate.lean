/-! Generic commutative-ring algebra behind the paid central two-clock
product and its two linear coefficients. Physical stages and payment
are hypotheses of the companion mathematical argument. -/
namespace RKResearch.ERK11CentralTwoClockProductGate

open Lean.Grind

variable {K : Type} [CommRing K]

theorem centralProduct
    (b z x y P Q VL VR H C1 C2 J I : K)
    (h1 : C1 - y*H = b*(z-y)*P*VR)
    (h2 : C2 - x*H = b*(z-x)*VL*Q)
    (hJ : J = b*P*Q)
    (hI : I = b*(z-x)*(z-y)*(VL*VR)) :
    (C1-y*H)*(C2-x*H)=J*I := by
  rw [h1,h2,hJ,hI]
  grind

theorem bilinearCoefficients
    (x y H C1 C2 J I0 I1 I2 : K)
    (h : (C1-y*H)*(C2-x*H) = J*(I2-(x+y)*I1+x*y*I0)) :
    (H^2-J*I0)*x*y + (J*I1-H*C1)*x +
      (J*I1-H*C2)*y + (C1*C2-J*I2) = 0 := by
  grind

theorem mobiusFactor
    (A B C D x y : K)
    (h : A*x*y+B*x+C*y+D=0) :
    (A*x+C)*(A*y+B)=-(A*D-B*C) := by
  grind

end RKResearch.ERK11CentralTwoClockProductGate

#print axioms RKResearch.ERK11CentralTwoClockProductGate.centralProduct
#print axioms RKResearch.ERK11CentralTwoClockProductGate.bilinearCoefficients
#print axioms RKResearch.ERK11CentralTwoClockProductGate.mobiusFactor
