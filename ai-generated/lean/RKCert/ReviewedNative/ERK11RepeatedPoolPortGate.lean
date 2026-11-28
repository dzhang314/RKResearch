/-! Scalar checks for the genuine repeated-inner-clock edge proof.
The actual paid support and normalized stage functionals are assumptions. -/
namespace RKResearch.ERK11RepeatedPoolPortGate

open Lean.Grind
variable {K : Type} [CommRing K]

theorem liveDormantFactor
    (z u I0 I1 I2 : K)
    (h : I2-u*I1=z*(I1-u*I0)) :
    I2-2*u*I1+u^2*I0=(z-u)*(I1-u*I0) := by
  grind

theorem averageResponse
    (r s a g1 g2 f1 f2 w1 w2 : K)
    (h : w1*f1+w2*f2=0) :
    w1*(r+f1*s+g1*a)+w2*(r+f2*s+g2*a) =
      (w1+w2)*r+(w1*g1+w2*g2)*a := by
  calc
    _ = (w1+w2)*r+(w1*g1+w2*g2)*a+(w1*f1+w2*f2)*s := by grind
    _ = _ := by rw [h]; grind

theorem poolDeterminant
    (p q r s t : K) (h1 : p+t*q=0) (h2 : r+t*s=0) :
    p*s-q*r=0 := by
  have hp : p=-(t*q) := by grind
  have hr : r=-(t*s) := by grind
  rw [hp,hr]
  grind

end RKResearch.ERK11RepeatedPoolPortGate

#print axioms RKResearch.ERK11RepeatedPoolPortGate.liveDormantFactor
#print axioms RKResearch.ERK11RepeatedPoolPortGate.averageResponse
#print axioms RKResearch.ERK11RepeatedPoolPortGate.poolDeterminant
