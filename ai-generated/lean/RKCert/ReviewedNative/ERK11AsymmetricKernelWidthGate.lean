/-! Scalar kernel compatibility for the two actual repeated-exclusive
contacts. The geometric mixed Gram hypotheses are separate. -/
namespace RKResearch.ERK11AsymmetricKernelWidthGate

open Lean.Grind
variable {K : Type} [CommRing K]

theorem kernelCompatibility
    (L0 L1 R0 R1 m0 m1 k0 k1 Ta Tb U : K)
    (hL : m0*L0+m1*L1=0)
    (hR : k0*R0+k1*R1=0)
    (hG : L0*R0+Ta*L1*R0+Tb*L0*R1+U*L1*R1=0) :
    (L1*R1)*(m1*k1-Ta*m0*k1-Tb*m1*k0+U*m0*k0)=0 := by
  have h1 : m1*L1=-(m0*L0) := by grind
  have h2 : k1*R1=-(k0*R0) := by grind
  calc
    _ = (m1*L1)*(k1*R1)-Ta*m0*L1*(k1*R1)-Tb*(m1*L1)*k0*R1+U*m0*k0*L1*R1 := by grind
    _ = (m0*k0)*(L0*R0+Ta*L1*R0+Tb*L0*R1+U*L1*R1) := by
      rw [h1,h2]
      grind
    _ = 0 := by
      rw [hG]
      grind

theorem affineConsistency
    (a b c d z y : K)
    (h : a*z*y+b*z+c*y+d=0)
    (h0 : a*z+c=0) :
    b*z+d=0 ∧ a*d-b*c=0 := by
  have h1 : b*z+d=0 := by grind
  have h2 : a*d-b*c=a*(b*z+d)-b*(a*z+c) := by grind
  rw [h0,h1] at h2
  grind

end RKResearch.ERK11AsymmetricKernelWidthGate

#print axioms RKResearch.ERK11AsymmetricKernelWidthGate.kernelCompatibility
#print axioms RKResearch.ERK11AsymmetricKernelWidthGate.affineConsistency
