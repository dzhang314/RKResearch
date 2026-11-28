import Lean.Elab.Tactic.Grind

namespace RKResearch.Certified.ERK10FourfoldInteriorScalars
open Lean.Grind

section Ring
variable {R : Type} [CommRing R]

def u2 (a t S T w : R) : R := 2*a*S+2*t*T-w*a^2
def g3 (a t S T w : R) : R := 3*a^2*S+3*t^2*T-w*a^3
def k4 (a t S T w : R) : R := 4*a^3*S+4*t^3*T-w*a^4
def F8 (a t S T w : R) : R :=
  2*k4 a t S T w + 3*a^2*u2 a t S T w - 5*a*g3 a t S T w + a^3*S

theorem feedback (a t S T w : R) (h : 2*t=3*a) :
    4*F8 a t S T w=9*a^3*T := by
  calc
    _=(4*(2*t)^3+12*a^2*(2*t)-15*a*(2*t)^2)*T := by
      clear h
      unfold F8 k4 u2 g3
      grind
    _=_ := by rw [h]; grind

theorem singletonSquare (a t s S T : R) (h : 2*t=3*a)
    (p2 : 2*(a*S+t*T)=s^2)
    (p3 : 3*(a^2*S+t^2*T)=s^3)
    (p4 : 9*a^3*S+8*t^3*T=2*s^4) :
    2*s^2*(s-t)^2=0 := by
  calc
    _=2*t^2*s^2-4*t*s^3+2*s^4 := by clear h p2 p3 p4; grind
    _=a*(2*t-3*a)^2*S := by rw [←p2,←p3,←p4]; grind
    _=0 := by rw [h]; grind

end Ring
section Field
variable {F : Type} [Field F]

theorem singletonExit (a t s S T : F) (two : (2:F) ≠ 0) (sn : s ≠ 0)
    (h : 2*t=3*a)
    (p2 : 2*(a*S+t*T)=s^2)
    (p3 : 3*(a^2*S+t^2*T)=s^3)
    (p4 : 9*a^3*S+8*t^3*T=2*s^4) : s=t := by
  have hh := singletonSquare a t s S T h p2 p3 p4
  grind

end Field
end RKResearch.Certified.ERK10FourfoldInteriorScalars
#print axioms RKResearch.Certified.ERK10FourfoldInteriorScalars.feedback
#print axioms RKResearch.Certified.ERK10FourfoldInteriorScalars.singletonSquare
#print axioms RKResearch.Certified.ERK10FourfoldInteriorScalars.singletonExit
