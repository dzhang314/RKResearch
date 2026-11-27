module

public import RKCert.ReviewedNative.ERK149AnchoredChronologyCensus

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKResearch.Certified.ERK149TwoPairRawTranspose

variable {K : Type*} [Field K] [CharZero K]

/-- Two paid scalar moments with one actually weighted earlier interior. -/
theorem one_weighted_site_two_moments (a t m : K) (ht : t ≠ 0)
    (h₁ : m*a=t^2/2) (h₂ : m*a^2=t^3/3) : t=3*a/2 := by
  have h : t^2*(t-3*a/2)=0 := by linear_combination 3*a*h₁-3*h₂
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left (pow_ne_zero 2 ht))

/-- In the early-ghost branch the second completion is forced to repeat
the first completion's site, irrespective of its use of the ghost donor. -/
theorem early_ghost_second_remainder (a s : K) (ha : a ≠ 0) :
    let t : K := 3*a/2
    (a+t)*s^3/3-a*t*s^2/2-s^4/4
      + (a^3/8)*(s^2*(3*t-2*s)/(6*a*(t-a))) =
        -s^2*(2*s-3*a)^2/16 := by
  let t : K := 3*a/2
  change (a+t)*s^3/3-a*t*s^2/2-s^4/4
      + (a^3/8)*(s^2*(3*t-2*s)/(6*a*(t-a))) = _
  have he : t-a≠0 := by
    have h : t-a=a/2 := by dsimp [t]; ring
    rw [h]
    exact div_ne_zero ha (by norm_num)
  field_simp [ha,he]
  dsimp [t]
  ring

/-- When the chronological middle donor is invisible to the scalar moments,
the three rooted reads resonate at twice the first clock. -/
theorem middle_ghost_resonance (c b t : K) (hc : c ≠ 0) (ht : t ≠ 0)
    (hT : (t-2*c)*t^3=0)
    (hQ : 6*b*c-4*(b+c)*t+3*t^2=0) :
    t=2*c ∧ b=2*c := by
  have he : t=2*c := sub_eq_zero.mp
    ((mul_eq_zero.mp hT).resolve_right (pow_ne_zero 3 ht))
  rw [he] at hQ
  have h : (2*c)*(2*c-b)=0 := by linear_combination hQ
  exact ⟨he,(sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left
    (mul_ne_zero (by norm_num) hc))).symm⟩

theorem doubled_site_cubic (c s : K) :
    (c+2*c)*s^3/3-c*(2*c)*s^2/2-s^4/4 = -s^2*(s-2*c)^2/4 := by
  ring

end RKResearch.Certified.ERK149TwoPairRawTranspose
