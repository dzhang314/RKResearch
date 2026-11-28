import Lean.Elab.Tactic.Grind

namespace RKResearch.Certified.ERK10ContiguousEndpointScalars
open Lean.Grind

section Ring
variable {R : Type} [CommRing R]

theorem forwardSecondDifference (r : R) :
    r^4-2*r^3+r^2=r^2*(r-1)^2 := by
  grind

theorem singleDonorFactors (a y w T : R)
    (p2 : 2*a*T=w*y^2) (p3 : 3*a^2*T=w*y^3)
    (p4 : 4*a^3*T=w*y^4) :
    (w*y^2)*(2*y-3*a)=0 ∧ (w*y^2)*(y^2-2*a^2)=0 := by
  constructor
  · calc
      _=3*a*(2*a*T-w*y^2)-2*(3*a^2*T-w*y^3) := by
        clear p2 p3 p4
        grind
      _=0 := by rw [p2,p3]; grind
  · calc
      _=2*a^2*(2*a*T-w*y^2)-(4*a^3*T-w*y^4) := by
        clear p2 p3 p4
        grind
      _=0 := by rw [p2,p4]; grind

end Ring
section Field
variable {F : Type} [Field F]

theorem singleDonorExit (a y w T : F) (an : a ≠ 0) (yn : y ≠ 0) (wn : w ≠ 0)
    (p2 : 2*a*T=w*y^2) (p3 : 3*a^2*T=w*y^3)
    (p4 : 4*a^3*T=w*y^4) : False := by
  obtain ⟨h2,h3⟩ := singleDonorFactors a y w T p2 p3 p4
  have hy : 2*y=3*a := by grind
  have hh : y^2=2*a^2 := by grind
  have hq : (2*y)^2=9*a^2 := by rw [hy]; grind
  have ha : a^2=0 := by grind
  grind
end Field

end RKResearch.Certified.ERK10ContiguousEndpointScalars
#print axioms RKResearch.Certified.ERK10ContiguousEndpointScalars.forwardSecondDifference
#print axioms RKResearch.Certified.ERK10ContiguousEndpointScalars.singleDonorExit
