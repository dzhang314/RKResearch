import Mathlib.Tactic.Ring

namespace RKResearch.Certified.ERK10FiveOpeningLeakageHeadScalars

variable {R : Type*} [CommRing R]

def K (a b z : R) : R := -3*z^2+4*(a+b)*z-6*a*b
def H (a b z : R) : R := -3*a*b+(2*b-a)*z

theorem immediate_a_closure (a b z : R) :
    K a b z*(a*b+3*a*z-2*b^2)-H a b z*(5*a*b-3*a*z-4*b^2+3*b*z)
      = 9*a*(a-z)*(b-z)^2 := by
  simp only [K,H]
  ring

theorem interleaved_a_closure (a b z : R) :
    K a b z*(2*a^2-a*b-3*b*z)-H b a z*(4*a^2-5*a*b-3*a*z+3*b*z)
      = -9*b*(a-z)^2*(b-z) := by
  simp only [K,H]
  ring

theorem two_helpers_before_closure (b c z : R) :
    H b c z*(-5*b*c+3*b*z+4*c^2-3*c*z)+K b c z*(b*c+3*b*z-2*c^2)
      = -9*b*(z-b)*(z-c)^2 := by
  simp only [K,H]
  ring

end RKResearch.Certified.ERK10FiveOpeningLeakageHeadScalars

#print axioms RKResearch.Certified.ERK10FiveOpeningLeakageHeadScalars.immediate_a_closure
#print axioms RKResearch.Certified.ERK10FiveOpeningLeakageHeadScalars.interleaved_a_closure
#print axioms RKResearch.Certified.ERK10FiveOpeningLeakageHeadScalars.two_helpers_before_closure
