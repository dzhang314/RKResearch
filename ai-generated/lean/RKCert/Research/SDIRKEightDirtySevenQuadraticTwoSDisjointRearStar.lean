import Mathlib.Tactic.Ring.Basic

namespace RKResearch.Certified.SDIRKEightDirtySevenQuadraticTwoSDisjointRearStar

variable {K : Type*} [CommRing K]

theorem scaled_front (L A B R f omega mu C Z J : K)
    (hL : L=f*(A+B*f)) (hC : C=A+B*R) (hZ : Z=omega*mu*C)
    (hJ : J=omega*mu*B) :
    omega*mu*L-f*Z=J*(f*(f-R)) := by
  rw [hL,hZ,hC,hJ]
  ring1

theorem scaled_rear (L A B R lam rho rhos omega mu C Z J : K)
    (hL : L=(lam*rho)*(A+B*(lam*rho))) (hC : C=A+B*R)
    (hZ : Z=omega*mu*C) (hJ : J=omega*mu*B) (hmu : mu=lam*rhos) :
    rhos^2*omega*L-rhos*rho*Z=J*rho*(mu*rho-rhos*R) := by
  rw [hL,hZ,hC,hJ,hmu]
  ring1

theorem eliminate_shared_scale (P X Y J k : K)
    (hX : X=J*k) (hY : Y=J*P) :
    P*X-Y*k=0 := by
  rw [hX,hY]
  ring1

end RKResearch.Certified.SDIRKEightDirtySevenQuadraticTwoSDisjointRearStar
