import Mathlib.Tactic.Ring.Basic

/-! Scalar ratio identities for the shared-endpoint closure. -/
namespace RKResearch.Certified.SDIRKEightDirtySevenQuadraticNoSharedEnd

variable {R : Type*} [CommRing R]

theorem shared_arithmetic_ratio (v b c : R) :
    ((1+4*v-4*v^2)*(-2+v+4*v^2-v^3)+4*v^2*(3*v-2))*(v^2-b*v+c) -
     (1+2*v-v^2)*(-2+v+4*v^2-v^3)*(4*v^2-2*b*v+c) =
    v*(1+2*v-v^2)*((-2+v+4*v^2-v^3)*(b-3*v)-
          (v-2)*(3*v-2)*(v^2-b*v+c)) := by
  ring1

theorem shared_terminal_scale_clear (beta k mu r w : R) :
    -beta*(k+mu)+2*beta*r*k*w = beta*(2*r*k*w-k-mu) := by
  ring1

end RKResearch.Certified.SDIRKEightDirtySevenQuadraticNoSharedEnd
