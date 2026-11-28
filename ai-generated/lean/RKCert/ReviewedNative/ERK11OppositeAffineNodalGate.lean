/-! Algebra of the opposite repeated-exclusive affine reduction.
The paid row statements and live nodal leading coefficient are
established by the companion mathematical argument. -/
namespace RKResearch.ERK11OppositeAffineNodalGate

open Lean.Grind
variable {K : Type} [CommRing K]

theorem bilinearReduce
    (d2 d1 d0 t z p00 p10 p01 p11 : K)
    (sum : d2*(t+z)=d1)
    (prod : d2*t*z=d0) :
    d2*(p00+p10*t+p01*z+p11*t*z)=
      d2*(p10-p01)*t+(d2*p00+d1*p01+d0*p11) := by
  rw [←sum,←prod]
  grind

theorem quadrilateralReduce
    (d2 d1 d0 t p0 p1 p2 : K)
    (nodal : d2*t^2-d1*t+d0=0) :
    d2*(p0+p1*t+p2*t^2)=
      (d2*p1+d1*p2)*t+(d2*p0-d0*p2) := by
  grind

theorem rankAffine
    (d2 a b c d t : K)
    (h1 : d2*a*t+b=0)
    (h2 : d2*c*t+d=0) : a*d-c*b=0 := by
  have hb : b = -(d2*a*t) := by grind
  have hd : d = -(d2*c*t) := by grind
  rw [hb,hd]
  grind

theorem normAffine
    (d2 d1 d0 a b t : K)
    (h1 : d2*a*t+b=0)
    (h2 : d2*t^2-d1*t+d0=0) :
    b^2+d1*a*b+d0*d2*a^2=0 := by
  have hb : b = -(d2*a*t) := by grind
  rw [hb]
  calc
    _ = d2*a^2*(d2*t^2-d1*t+d0) := by grind
    _ = 0 := by
      rw [h2]
      grind

end RKResearch.ERK11OppositeAffineNodalGate

#print axioms RKResearch.ERK11OppositeAffineNodalGate.bilinearReduce
#print axioms RKResearch.ERK11OppositeAffineNodalGate.quadrilateralReduce
#print axioms RKResearch.ERK11OppositeAffineNodalGate.rankAffine
#print axioms RKResearch.ERK11OppositeAffineNodalGate.normAffine
