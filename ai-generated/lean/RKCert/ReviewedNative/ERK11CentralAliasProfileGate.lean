/-! Portable scalar gates for the nonzero-pool symmetric-central-alias exit. -/
namespace RKResearch.ERK11CentralAliasProfileGate
open Lean.Grind
variable {R : Type} [CommRing R]

theorem clearedOuterProfile
    (p v vcal fresh g delta f : R)
    (hprofile : p*(vcal-v)+fresh=0)
    (horth : delta*f+v*g=0) :
    p*(vcal*g+delta*f)+fresh*g=0 := by
  have ei : delta*f= -(v*g) := by grind
  rw [ei]
  calc
    p*(vcal*g+ -(v*g))+fresh*g = (p*(vcal-v)+fresh)*g := by grind
    _ = 0 := by rw [hprofile]; grind

theorem clearCentralDiagonal
    (w p pAt qAt eps mu aDot dDot j u v : R)
    (hm : pAt*eps=p-pAt*mu)
    (hj : w*p=j)
    (hd : w*(dDot+eps*aDot)=qAt)
    (hu : u=v*w) :
    u*pAt*dDot+(v*j-u*pAt*mu)*aDot=v*pAt*qAt := by
  calc
    u*pAt*dDot+(v*j-u*pAt*mu)*aDot
       = v*(w*pAt*dDot+w*(p-pAt*mu)*aDot) := by rw [hu,←hj]; grind
    _ = v*pAt*(w*(dDot+eps*aDot)) := by rw [←hm]; grind
    _ = v*pAt*qAt := by rw [hd]

theorem reflectedFirstExtra
    (r₀ r₁ w y d : R)
    (h : r₀*(w-d)*(y-d)-r₁*(1-w)*(1-y)=0) :
    (r₀*(w-d)+r₁*(1-w))*y=r₀*(w-d)*d+r₁*(1-w) := by
  have E :
      (r₀*(w-d)+r₁*(1-w))*y-(r₀*(w-d)*d+r₁*(1-w)) =
        r₀*(w-d)*(y-d)-r₁*(1-w)*(1-y) := by grind
  rw [h] at E
  grind

theorem proportionalFirstRows
    (p₀ p₁ s₀ s₁ k : R) (h0 : p₀=k*s₀) (h1 : p₁=k*s₁) :
    p₀*s₁-p₁*s₀=0 := by
  rw [h0,h1]
  grind

end RKResearch.ERK11CentralAliasProfileGate
#print axioms RKResearch.ERK11CentralAliasProfileGate.clearedOuterProfile
#print axioms RKResearch.ERK11CentralAliasProfileGate.clearCentralDiagonal
#print axioms RKResearch.ERK11CentralAliasProfileGate.reflectedFirstExtra
#print axioms RKResearch.ERK11CentralAliasProfileGate.proportionalFirstRows
