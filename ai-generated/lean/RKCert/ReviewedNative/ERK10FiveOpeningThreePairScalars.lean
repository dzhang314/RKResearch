import Lean.Elab.Tactic.Grind

namespace RKResearch.Certified.ERK10FiveOpeningThreePairScalars
open Lean.Grind

section Ring
variable {F : Type} [CommRing F]

def N (x i j : F) : F := 3*x^2 - 4*(i+j)*x + 6*i*j

theorem primitiveTap (z j k x a b c : F)
    (p2 : 2*(a*z+b*j+c*k)=x^2)
    (p3 : 3*(a*z^2+b*j^2+c*k^2)=x^3)
    (p4 : 4*(a*z^3+b*j^3+c*k^3)=x^4) :
    12*j*(j-z)*(j-k)*b=x^2*N x z k := by
  calc
    _=3*(4*(a*z^3+b*j^3+c*k^3))
      -4*(z+k)*(3*(a*z^2+b*j^2+c*k^2))
      +6*z*k*(2*(a*z+b*j+c*k)) := by
        clear p2 p3 p4
        grind
    _=x^2*N x z k := by
        rw [p2,p3,p4]
        unfold N
        grind

theorem tapDeterminant (z j k : F) :
    N z z k * N j z j - N z z j * N j z k
      = -6*z*(z-j)^2*(j-k) := by
  unfold N
  grind

theorem eliminationAtClosures (z j k a b : F)
    (first : N z z k*a+N z z j*b=0)
    (second : N j z k*a+N j z j*b=0) :
    (-6*z*(z-j)^2*(j-k))*a=0 ∧ (-6*z*(z-j)^2*(j-k))*b=0 := by
  rw [←tapDeterminant]
  constructor
  · calc
      _ = N j z j*(N z z k*a+N z z j*b)
          - N z z j*(N j z k*a+N j z j*b) := by clear first second; grind
      _ = 0 := by rw [first,second]; grind
  · calc
      _ = N z z k*(N j z k*a+N j z j*b)
          - N j z k*(N z z k*a+N z z j*b) := by clear first second; grind
      _ = 0 := by rw [first,second]; grind

theorem leakageSquare (c z ell t : F)
    (p2 : c^2*ell+2*c*t=z^2)
    (p3 : c^3*ell+3*c^2*t=z^3)
    (p4 : c^4*ell+4*c^3*t=z^4) :
    z^2*(z-c)^2=0 := by
  calc
    _ = c^2*z^2-2*c*z^3+z^4 := by clear p2 p3 p4; grind
    _ = 0 := by rw [←p2,←p3,←p4]; grind

end Ring

section Field
variable {F : Type} [Field F]

theorem opposedExit (z j k a b : F)
    (six : (6:F) ≠ 0) (nz : z ≠ 0) (zj : z ≠ j) (jk : j ≠ k)
    (first : N z z k*a+N z z j*b=0)
    (second : N j z k*a+N j z j*b=0) :
    a=0 ∧ b=0 := by
  have hd : (-6*z*(z-j)^2*(j-k) : F) ≠ 0 := by grind
  obtain ⟨ha,hb⟩ := eliminationAtClosures z j k a b first second
  exact ⟨by grind, by grind⟩

theorem leakageExit (c z ell t : F) (nz : z ≠ 0)
    (p2 : c^2*ell+2*c*t=z^2)
    (p3 : c^3*ell+3*c^2*t=z^3)
    (p4 : c^4*ell+4*c^3*t=z^4) : z=c := by
  have h := leakageSquare c z ell t p2 p3 p4
  grind

end Field

end RKResearch.Certified.ERK10FiveOpeningThreePairScalars

#print axioms RKResearch.Certified.ERK10FiveOpeningThreePairScalars.primitiveTap
#print axioms RKResearch.Certified.ERK10FiveOpeningThreePairScalars.tapDeterminant
#print axioms RKResearch.Certified.ERK10FiveOpeningThreePairScalars.opposedExit
#print axioms RKResearch.Certified.ERK10FiveOpeningThreePairScalars.leakageExit
