import Mathlib.Tactic.Ring.Basic

namespace RKResearch.Certified.SDIRKEightDirtySevenQuadraticTwoSOneExtraTerminalOverlap

variable {K : Type*} [CommRing K]

theorem front_singleton_scaled (L A B lam T beta f : K)
    (hL : L=f*(A+B*f)) (hT : T=lam*A) (hb : beta=lam*B) :
    f*T+beta*f^2-lam*L=0 := by
  rw [hL,hT,hb]
  ring1

theorem rear_singleton_scaled (L A B lam T beta rho : K)
    (hL : L=(lam*rho)*(A+B*(lam*rho))) (hT : T=lam*A) (hb : beta=lam*B) :
    rho*T+beta*lam*rho^2-L=0 := by
  rw [hL,hT,hb]
  ring1

end RKResearch.Certified.SDIRKEightDirtySevenQuadraticTwoSOneExtraTerminalOverlap
