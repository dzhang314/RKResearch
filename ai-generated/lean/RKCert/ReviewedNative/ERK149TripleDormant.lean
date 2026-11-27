module

public import RKCert.ReviewedNative.ERK149DormantOpposition

import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKResearch.Certified.ERK149TripleDormant

variable {K : Type*} [Field K] [CharZero K]

/-- Exact two-entry determinant on the two earliest repeated-clock rows. -/
theorem early_defect_plane (a w v k : K) :
    (-(a^2*w/2))*(-(a^3*v/6)) -
      (k*a*w-a^2*v/2)*(-(a^3*w/6)) = k*a^4*w^2/6 := by
  ring

/-- The paid second and third moments fix the first chronology resonance
without solving for either donor tap. -/
theorem post_triple_anchor_first_resonance
    (a c t nu lam : K) (ht : t ≠ 0)
    (hg : nu*a^3 + 3*a*lam*c^2 - 2*lam*c^3 = 0)
    (h₂ : nu*a^2+lam*c^2=t^3/3) (h₃ : nu*a^3+lam*c^3=t^4/4) :
    t=2*a := by
  have h : t^3*(t-2*a)=0 := by linear_combination -2*hg+6*a*h₂-4*h₃
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left (pow_ne_zero 3 ht))

/-- The two late opposite taps consume just the honest products x and z,
even when some physical weight vanishes. -/
theorem internal_anchor_first_resonance
    (a c t nu lam x z : K) (ha : a ≠ 0) (ht : t ≠ 0)
    (hu : -nu*a^2/2+a*x+c*z=0)
    (hh : -a^2*x/2-lam*a*c^2/4=0)
    (hg : -nu*a^3/3+a^2*x+c^2*z+lam*c^2*(3*a-2*c)/6=0)
    (h₂ : nu*a^2+lam*c^2=t^3/3) (h₃ : nu*a^3+lam*c^3=t^4/4) :
    t=2*c := by
  have hax₀ : a*(a*x+lam*c^2/2)=0 := by linear_combination -2*hh
  have hax : a*x+lam*c^2/2=0 := (mul_eq_zero.mp hax₀).resolve_left ha
  have hz : c*z=t^3/6 := by linear_combination hu-hax+h₂/2
  have hcz : c^2*z=t^4/12 := by linear_combination hg+2*hh+h₃/3
  have h : t^3*(t-2*c)=0 := by linear_combination 12*c*hz-12*hcz
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left (pow_ne_zero 3 ht))

end RKResearch.Certified.ERK149TripleDormant
