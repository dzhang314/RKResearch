/-! Scalar cancellations in the same-clock repeated-exclusive
anchored row contact. The actual row and payment are hypotheses. -/
namespace RKResearch.ERK11RepeatedExclusiveContactGate

open Lean.Grind
variable {K : Type} [CommRing K]

theorem massFactor (b f r g B : K)
    (h : b*f + r*g = 0) (m : B=b+r) :
    f*B-r*(f-g)=0 := by
  grind

theorem weightedContact
    (s b B V U P D A gamma M : K)
    (hMass : b*s=B)
    (hProduct : gamma=B*V*U)
    (hPrimitive : M=b*P*U)
    (hRead : s*D+30*P*A=0) :
    gamma*D+30*V*M*A=0 := by
  calc
    _ = b*V*U*(s*D+30*P*A) := by
      rw [hProduct,hPrimitive,←hMass]
      grind
    _ = 0 := by rw [hRead]; grind

theorem clearMarkedClock
    (g m i j k V D A I J : K)
    (hG : g*(i-j)*(i-k)=I)
    (hM : m*(i-k)=J)
    (hContact : g*D+30*V*m*A=0) :
    I*D+30*V*(i-j)*J*A=0 := by
  calc
    _ = (i-j)*(i-k)*(g*D+30*V*m*A) := by
      rw [←hG,←hM]
      grind
    _ = 0 := by rw [hContact]; grind

end RKResearch.ERK11RepeatedExclusiveContactGate

#print axioms RKResearch.ERK11RepeatedExclusiveContactGate.weightedContact
#print axioms RKResearch.ERK11RepeatedExclusiveContactGate.clearMarkedClock
#print axioms RKResearch.ERK11RepeatedExclusiveContactGate.massFactor
