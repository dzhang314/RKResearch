module

public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8SharedClockReceipts

open Polynomial

/-- The two affine readings determine the literal defect if either slope
is nonzero, including at a clock already used by an earlier row. -/
theorem affineReadUnique {K : Type*} [Field K] (a b c d x y : K)
    (hu : b≠0 ∨ d≠0)
    (hax : a+b*x=0) (hay : a+b*y=0) (hcx : c+d*x=0) (hcy : c+d*y=0) :
    x=y := by
  rcases hu with hb | hd
  · apply mul_left_cancel₀ hb
    exact add_left_cancel (hax.trans hay.symm)
  · apply mul_left_cancel₀ hd
    exact add_left_cancel (hcx.trans hcy.symm)

/-- One supported discrepancy row cannot have a nonzero cubic defect
when the paid pairing vanishes and its output weight is nonzero. -/
theorem singletonPairing {K : Type*} [Field K] (b u h : K)
    (hb : b≠0) (hu : u≠0) (hp : b*u*h=0) : h=0 :=
  (mul_eq_zero.mp hp).resolve_left (mul_ne_zero hb hu)

/-- Cancellation in the dual defect profiles controls the remaining
degree budget, independently of clock collisions or output signs. -/
theorem reducedDualBudget {K : Type*} [Field K] {p q r s : K[X]}
    (hc : IsCoprime p q) (hq : q≠0) (hr : r≠0) (he : q*s=r*p) :
    ∃ w : K[X], w≠0 ∧ r=q*w ∧ s=p*w ∧ r.natDegree=q.natDegree+w.natDegree := by
  obtain ⟨w,hw⟩ := hc.symm.dvd_of_dvd_mul_right (show q ∣ r*p from ⟨s,he.symm⟩)
  have hw0 : w≠0 := by
    intro h
    exact hr (by simp [hw,h])
  refine ⟨w,hw0,hw,mul_left_cancel₀ hq ?_,?_⟩
  · rw [he,hw]
    ring
  · rw [hw,natDegree_mul hq hw0]

/-- Weighted variance of a double clock, valid with signed weights and in
an arbitrary commutative ring. -/
theorem doubleClockVariance {R : Type*} [CommRing R] (u v x y : R) :
    (u+v)*(u*x^2+v*y^2)-(u*x+v*y)^2=u*v*(x-y)^2 := by ring

end RKCert.ReviewedNative.SDIRK8SharedClockReceipts
