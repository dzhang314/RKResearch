/-! Scalar Hankel identities for the genuine same-free-pair clock atlas.
The actual moment and mixed tableau transfer are separate. -/
namespace RKResearch.ERK11TwoFreeShiftedHankelGate

open Lean.Grind
variable {K : Type} [CommRing K]

theorem shiftedCramer
    (e0 e1 e2 e3 S P : K)
    (h0 : e0*P-e1*S+e2=0)
    (h1 : e1*P-e2*S+e3=0) :
    (e0*e2-e1^2)*S=e0*e3-e1*e2 ∧
      (e0*e2-e1^2)*P=e1*e3-e2^2 := by
  have hs : (e0*e2-e1^2)*S-(e0*e3-e1*e2) =
      e1*(e0*P-e1*S+e2)-e0*(e1*P-e2*S+e3) := by grind
  have hp : (e0*e2-e1^2)*P-(e1*e3-e2^2) =
      e2*(e0*P-e1*S+e2)-e1*(e1*P-e2*S+e3) := by grind
  rw [h0,h1] at hs hp
  grind

theorem hankelThree
    (z t s wz wt ws m0 m1 m2 m3 m4 : K)
    (h0 : m0=wz+wt+ws)
    (h1 : m1=wz*z+wt*t+ws*s)
    (h2 : m2=wz*z^2+wt*t^2+ws*s^2)
    (h3 : m3=wz*z^3+wt*t^3+ws*s^3)
    (h4 : m4=wz*z^4+wt*t^4+ws*s^4) :
    m0*(m2*m4-m3^2)-m1*(m1*m4-m2*m3)+m2*(m1*m3-m2^2) =
      wz*wt*ws*(z-t)^2*(z-s)^2*(t-s)^2 := by
  rw [h0,h1,h2,h3,h4]
  grind

theorem shiftedMinorsExpand
    (z m0 m1 m2 m3 m4 e0 e1 e2 e3 : K)
    (h0 : e0=m1-z*m0) (h1 : e1=m2-z*m1)
    (h2 : e2=m3-z*m2) (h3 : e3=m4-z*m3) :
    m0*(m2*m4-m3^2)-m1*(m1*m4-m2*m3)+m2*(m1*m3-m2^2) =
      m0*(e1*e3-e2^2)-m1*(e0*e3-e1*e2)+m2*(e0*e2-e1^2) := by
  rw [h0,h1,h2,h3]
  grind

end RKResearch.ERK11TwoFreeShiftedHankelGate

#print axioms RKResearch.ERK11TwoFreeShiftedHankelGate.shiftedCramer
#print axioms RKResearch.ERK11TwoFreeShiftedHankelGate.hankelThree
#print axioms RKResearch.ERK11TwoFreeShiftedHankelGate.shiftedMinorsExpand
