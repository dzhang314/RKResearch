import Mathlib.Tactic.Ring.Basic

namespace RKResearch.Certified.SDIRKEightDirtySevenBothSingletonOneSharedDouble

variable {K : Type*} [CommRing K]

theorem paid_endpoint_quadratic_gate (a b c H p s : K) :
    let T : K → K := fun z => a+b*z+c*z^2
    let L : K → K := fun z => (H-z)*T 0+z*T H
    p*(p-H)*(H*T s-L s)-s*(s-H)*(H*T p-L p)=0 := by
  dsimp
  ring1

theorem scale_shared_vieta (A B lam f rho beta : K)
    (hA : A = -B*(f+lam*rho)) (hbeta : beta = B*lam) :
    lam*A = -beta*(f+lam*rho) := by
  rw [hA,hbeta]
  ring1

end RKResearch.Certified.SDIRKEightDirtySevenBothSingletonOneSharedDouble
