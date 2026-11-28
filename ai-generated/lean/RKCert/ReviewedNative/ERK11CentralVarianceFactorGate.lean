/-! Scalar arithmetic for central repeated-pair primitive normalization
and the zero-variance width fiber. The paid model transfer is separate. -/
namespace RKResearch.ERK11CentralVarianceFactorGate

open Lean.Grind
variable {K : Type} [CommRing K]

theorem cancelDormantPrimitive
    (z u I M P A V : K)
    (hI : I=(z-u)*M)
    (hP : I*P=A*(z-u)*V) :
    (z-u)*(M*P-A*V)=0 := by
  rw [hI] at hP
  grind

theorem zeroVarianceMask
    (I0 I1 I2 u : K)
    (h : I0*I2-I1^2=0) :
    I0*(I2-u*I1)=I1*(I1-u*I0) := by
  grind

theorem quadraticAtRoot
    (A B C u u0 : K)
    (h : A*u0^2+B*u0+C=0) :
    A*u^2+B*u+C=(u-u0)*(A*u+B+A*u0) := by
  grind

theorem reflectedBilinearCoefficient
    (H C1 C2 J I u : K) :
    ((H-C2)-(1-u)*H)*((H-C1)-(1-u)*H)-J*I =
      (C1-u*H)*(C2-u*H)-J*I := by
  grind

end RKResearch.ERK11CentralVarianceFactorGate

#print axioms RKResearch.ERK11CentralVarianceFactorGate.cancelDormantPrimitive
#print axioms RKResearch.ERK11CentralVarianceFactorGate.zeroVarianceMask
#print axioms RKResearch.ERK11CentralVarianceFactorGate.quadraticAtRoot
#print axioms RKResearch.ERK11CentralVarianceFactorGate.reflectedBilinearCoefficient
