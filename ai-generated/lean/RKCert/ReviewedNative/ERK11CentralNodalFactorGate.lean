/-! Scalar identities for the two real shifted nodal rows.
The equations are explicit assumptions; no tableau transfer is encoded. -/
namespace RKResearch.ERK11CentralNodalFactorGate

open Lean.Grind
variable {K : Type} [CommRing K]

theorem nodalFactor
    (m0 m1 m2 m3 z t X : K)
    (h0 : m2 = (z+t)*m1 - z*t*m0)
    (h1 : m3 = (z+t)*m2 - z*t*m1) :
    (m1-X*m0)*(m3-X*m2) - (m2-X*m1)^2 =
    (m0*m2-m1^2)*(X-z)*(X-t) := by
  rw [h1,h0]
  grind

theorem liveMinor
    (m0 m1 m2 z t : K)
    (h : m2 = (z+t)*m1 - z*t*m0) :
    m0*m2-m1^2 = -((m1-z*m0)*(m1-t*m0)) := by
  rw [h]
  grind

theorem derivativeAtDormant
    (m0 m1 m2 m3 z t : K)
    (h0 : m2 = (z+t)*m1 - z*t*m0)
    (h1 : m3 = (z+t)*m2 - z*t*m1) :
    2*(m0*m2-m1^2)*z-(m0*m3-m1*m2) =
      (m0*m2-m1^2)*(z-t) := by
  rw [h1,h0]
  grind

theorem singularRows
    (m0 m1 m2 m3 z : K)
    (h0 : m1-z*m0=0) (h1 : m2-z*m1=0) (h2 : m3-z*m2=0) :
    m1=z*m0 ∧ m2=z^2*m0 ∧ m3=z^3*m0 := by
  grind

theorem twoSitePivots
    (z t wz wt m0 m1 m2 : K)
    (h0 : m0 = wz+wt)
    (h1 : m1 = wz*z+wt*t)
    (h2 : m2 = wz*z^2+wt*t^2) :
    m1-z*m0 = (t-z)*wt ∧
    m0*m2-m1^2 = wz*wt*(z-t)^2 := by
  rw [h0,h1,h2]
  grind

end RKResearch.ERK11CentralNodalFactorGate

#print axioms RKResearch.ERK11CentralNodalFactorGate.nodalFactor
#print axioms RKResearch.ERK11CentralNodalFactorGate.liveMinor
#print axioms RKResearch.ERK11CentralNodalFactorGate.derivativeAtDormant
#print axioms RKResearch.ERK11CentralNodalFactorGate.singularRows
#print axioms RKResearch.ERK11CentralNodalFactorGate.twoSitePivots
