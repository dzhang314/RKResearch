/-! Cleared endpoint and temporal identities for a singular sparse fixed block. -/
namespace RKResearch.ERK11NeighborNonsharedRightArithmetic
open Lean.Grind

theorem fixedNullEndpointRatio {R : Type} [CommRing R]
    (w h l0 l1 T r0 rw : R)
    (hw : w = 2*h)
    (h0 : r0 = -h*w*l0*T)
    (h1 : rw = h*w*l1*T) :
    l0*rw+l1*r0=0 := by
  subst w
  subst r0
  subst rw
  grind

theorem fixedNullTemporal {R : Type} [CommRing R]
    (w l0 l1 E E0 r0 rw rx : R)
    (hr : l0*rw+l1*r0=0) :
    -(w*l0*E*rw)-w*l1*E0*rx =
      w*l1*(E*r0-E0*rx) := by
  have hm : l0*rw=-(l1*r0) := by grind
  calc
    -(w*l0*E*rw)-w*l1*E0*rx =
        -(w*E*(l0*rw))-w*l1*E0*rx := by grind
    _ = w*l1*(E*r0-E0*rx) := by rw [hm]; grind

end RKResearch.ERK11NeighborNonsharedRightArithmetic
#print axioms RKResearch.ERK11NeighborNonsharedRightArithmetic.fixedNullEndpointRatio
#print axioms RKResearch.ERK11NeighborNonsharedRightArithmetic.fixedNullTemporal
