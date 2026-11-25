module

public import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Ring.Basic

@[expose] public section

/-! # Signed two-point moment elimination over an ordered field -/
namespace RKCert.ReviewedNative.OrderedTwoPointMoments

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The exact two-point moments, including the signed affine identities.
Only the centroid bounds require positivity of the total mass. -/
structure Reconstruction (lo hi mL mR mass moment : K) : Prop where
  left_num : mL * (hi-lo) = hi*mass-moment
  right_num : mR * (hi-lo) = moment-lo*mass
  left_mass : mL = (hi*mass-moment)/(hi-lo)
  right_mass : mR = (moment-lo*mass)/(hi-lo)
  affine : ∀ b c : K, mL*(b+c*lo) + mR*(b+c*hi) = b*mass+c*moment
  affine_at_centroid : mass ≠ 0 →
    ∀ b c : K, mL*(b+c*lo) + mR*(b+c*hi) = mass*(b+c*(moment/mass))
  centroid_closed_iff : 0 < mass →
    ((0 ≤ mL ∧ 0 ≤ mR) ↔ lo ≤ moment/mass ∧ moment/mass ≤ hi)
  centroid_strict_iff :
    (0 < mL ∧ 0 < mR) ↔ 0 < mass ∧ lo < moment/mass ∧ moment/mass < hi

/-- Eliminate the two masses with no sign or nonzero-total assumption.
The converse recovers the full moment equations from the affine law. -/
theorem two_point_moment_elimination
    {lo hi mL mR mass moment : K} (ordered : lo < hi) :
    (mL+mR = mass ∧ lo*mL+hi*mR = moment) ↔
      Reconstruction lo hi mL mR mass moment := by
  constructor
  · rintro ⟨mass_eq, moment_eq⟩
    have gap : 0 < hi-lo := sub_pos.mpr ordered
    have ln : mL*(hi-lo) = hi*mass-moment := by
      rw [← mass_eq, ← moment_eq]
      ring1
    have rn : mR*(hi-lo) = moment-lo*mass := by
      rw [← mass_eq, ← moment_eq]
      ring1
    have lm : mL = (hi*mass-moment)/(hi-lo) := (eq_div_iff gap.ne').mpr ln
    have rm : mR = (moment-lo*mass)/(hi-lo) := (eq_div_iff gap.ne').mpr rn
    have affine (b c : K) : mL*(b+c*lo) + mR*(b+c*hi) = b*mass+c*moment := by
      rw [← mass_eq, ← moment_eq]
      ring1
    have centered (nz : mass ≠ 0) (b c : K) :
        mL*(b+c*lo) + mR*(b+c*hi) = mass*(b+c*(moment/mass)) := by
      calc
        _ = b*mass+c*moment := affine b c
        _ = b*mass+c*((moment/mass)*mass) := by rw [div_mul_cancel₀ _ nz]
        _ = _ := by ring1
    have lnng : 0 ≤ mL ↔ moment ≤ hi*mass := by
      rw [lm, le_div_iff₀ gap, zero_mul, sub_nonneg]
    have rnng : 0 ≤ mR ↔ lo*mass ≤ moment := by
      rw [rm, le_div_iff₀ gap, zero_mul, sub_nonneg]
    have lp : 0 < mL ↔ moment < hi*mass := by
      rw [lm, div_pos_iff_of_pos_right gap, sub_pos]
    have rp : 0 < mR ↔ lo*mass < moment := by
      rw [rm, div_pos_iff_of_pos_right gap, sub_pos]
    have closed (mp : 0 < mass) :
        (0 ≤ mL ∧ 0 ≤ mR) ↔ lo ≤ moment/mass ∧ moment/mass ≤ hi := by
      rw [lnng, rnng, le_div_iff₀ mp, div_le_iff₀ mp]
      exact and_comm
    have opened (mp : 0 < mass) :
        (0 < mL ∧ 0 < mR) ↔ lo < moment/mass ∧ moment/mass < hi := by
      rw [lp, rp, lt_div_iff₀ mp, div_lt_iff₀ mp]
      exact and_comm
    have strict : (0 < mL ∧ 0 < mR) ↔
        0 < mass ∧ lo < moment/mass ∧ moment/mass < hi := by
      constructor
      · intro hp
        have mp : 0 < mass := by
          rw [← mass_eq]
          exact add_pos hp.1 hp.2
        exact ⟨mp, (opened mp).mp hp⟩
      · rintro ⟨mp, hiOpen⟩
        exact (opened mp).mpr hiOpen
    exact ⟨ln, rn, lm, rm, affine, centered, closed, strict⟩
  · intro facts
    refine ⟨?_, ?_⟩
    · simpa only [zero_mul, add_zero, mul_one, one_mul] using facts.affine 1 0
    · have moment_form : mL*lo+mR*hi = moment := by
        simpa only [one_mul, zero_add, zero_mul] using facts.affine 0 1
      simpa only [mul_comm mL lo, mul_comm mR hi] using moment_form

end RKCert.ReviewedNative.OrderedTwoPointMoments