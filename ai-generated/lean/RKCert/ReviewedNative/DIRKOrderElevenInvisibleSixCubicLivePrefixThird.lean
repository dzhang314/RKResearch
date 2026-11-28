module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Commute.Units
import Mathlib.Tactic.LinearCombination

@[expose] public section

/-! # Unit carrier prefix and actual third-ghost scalar gates -/
namespace RKResearch.Certified.Graded.OrderElevenInvisibleSixCubicLivePrefixThird

section Ring
variable {K : Type*} [CommRing K]

/-- Nonzero hull multipliers and the clean hull unit
make both factors of the paid prefix relation units. -/
theorem prefix_quotient_units (x ξ j ell s : K)
    (hell : IsUnit ell) (hs : IsUnit s) (h : (x-ξ)*j=ell*s) :
    IsUnit (x-ξ) ∧ IsUnit j := by
  have hu : IsUnit ((x-ξ)*j) := by
    rw [h]
    exact hell.mul hs
  have hc : Commute (x-ξ) j := mul_comm _ _
  exact hc.isUnit_mul_iff.mp hu

/-- In the carrier quotient, the ratio is literally affine. -/
theorem prefix_ratio_identity (x ξ j jInv ell s t : K)
    (hj : j*jInv=1) (ht : t=s*jInv) (h : (x-ξ)*j=ell*s) :
    ell*t=x-ξ := by
  rw [ht,←mul_assoc,←h,mul_assoc,hj,mul_one]

/-- The affine constant and linear coefficients give a
denominator-free location relation. -/
theorem prefix_location_clear (ell ξ t₀ t₁ : K)
    (h₀ : ell*t₀= -ξ) (h₁ : ell*t₁=1) : ξ*t₁+t₀=0 := by
  linear_combination t₁*h₀-t₀*h₁

/-- Once the actual third diagonal is known, its tap from the
second ghost has this exact cleared expression. -/
theorem third_gap_tap (u z w c d t q : K)
    (hq : q=c*(u-z)*(u-w)) (ht : (w-z)*t+(u-z)*d=q)
    (hd : (1+c)*d=c*(u-w)) :
    (1+c)*(w-z)*t=c^2*(u-z)*(u-w) := by
  linear_combination (1+c)*(ht+hq)-(u-z)*hd
end Ring

/-- The second zero output of the marked gap vector makes
the actual third diagonal equation independent of an
unknown earlier tap. -/
theorem third_gap_diagonal {K : Type*} [Field K] (u z w c d t q : K)
    (hz : u≠z) (hw : u≠w)
    (hq : q=c*(u-z)*(u-w)) (ht : (w-z)*t+(u-z)*d=q)
    (hc : (u-w)*(w-z)*t=d*q) :
    (1+c)*d=c*(u-w) := by
  have h : (u-z)*(u-w)*((1+c)*d-c*(u-w))=0 := by
    linear_combination (u-w)*ht-hc-(d-(u-w))*hq
  exact sub_eq_zero.mp
    ((mul_eq_zero.mp h).resolve_left (mul_ne_zero (sub_ne_zero.mpr hz) (sub_ne_zero.mpr hw)))

/-- A true distinct root permits a polynomial divided difference.
No numeric residue difference is inverted. -/
theorem divided_quintic {K : Type*} [Field K] (z w uz uw fz fw du df : K)
    (hzw : w≠z) (hu : uw-uz=(w-z)*du) (hf : fw-fz=(w-z)*df)
    (h : fw*uz-fz*uw=0) : uz*df-fz*du=0 := by
  have h0 : (w-z)*(uz*df-fz*du)=0 := by
    linear_combination h-uz*hf+fz*hu
  exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hzw)

/-- Dividing the exact commutator crossing by the characteristic-zero
difference gives a formula evaluable even at coincident residues. -/
theorem divided_commutator {K : Type*} [Field K] (z w uz uw d t du dt : K)
    (hzw : w≠z) (hu : uw-uz=(w-z)*du) (ht : t-d=(w-z)*dt)
    (h : uz*(w-z-d)*t+uw*d^2=0) :
    uz*t-uz*d*dt+d^2*du=0 := by
  have h0 : (w-z)*(uz*t-uz*d*dt+d^2*du)=0 := by
    linear_combination h+uz*d*ht-d^2*hu
  exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hzw)

end RKResearch.Certified.Graded.OrderElevenInvisibleSixCubicLivePrefixThird
