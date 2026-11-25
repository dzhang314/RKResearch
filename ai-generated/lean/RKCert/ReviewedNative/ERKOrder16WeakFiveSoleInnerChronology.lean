module

public import RKCert.ReviewedNative.WeakFiveSoleInnerPaidErasure
public import RKCert.ReviewedNative.ERKOrder16WeakFiveSoleInnerUniformCaps

import Mathlib.Tactic.Ring

@[expose] public section

/-! # Exact paid chronology and completion of the literal SoleInner sector

The retained stop, the surviving label and the erased label in the three
applications are respectively (z,h,u), (h,u,z), and (z,u,h). They
use the two actual outer words at z, the actual backward-inner word
at h, and the same three original signed masses. -/
namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

open Polynomial
open RKCert.ReviewedNative.PositiveRule19
open RKCert.ReviewedNative.WeakFive16
open RKCert.ReviewedNative.WeakFiveSoleInner
open RKCert.ReviewedNative.WeakFiveSoleInnerChronology

universe u
noncomputable section
variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Chronology and the two actual adjacent sign changes, with no assumptions
on the signs of original output weights. -/
theorem paid_inner_chronology_of_ports {a e u h z r₀ r₁ r₂ : K}
    (B : OrientedPorts a e u h z r₀ r₁ r₂) : PaidInnerChronology e u h z r₀ r₁ r₂ := by
  let q := profile e r₀ r₁ r₂
  obtain ⟨η,law,signs⟩ := signed_law_of_ports B
  have zM : z∈({z,h,u} : Finset K) := by simp
  have hM : h∈({z,h,u} : Finset K) := by simp
  have uM : u∈({z,h,u} : Finset K) := by simp
  have zLive : q.eval z≠0 := B.marksLive z zM
  have hLive : q.eval h≠0 := B.marksLive h hM
  have zScale := signs z zM
  have hScale := signs h hM
  have uScale := signs u uM
  have a0 := B.ae.trans B.eNeg
  have head : integral z 1 ((1-X)*(X-C u)*q)=0 :=
    right_pair_pays_erasure B.reverseFirst B.reverseSecond
  obtain ⟨zh,zhTilt⟩ := actual_right_erasure a0 B.eNeg B.zUnit B.hUnit B.hz B.zu.ne'
    zLive law zScale hScale head
  have middle : integral h 1 ((1-X)*(X-C z)*q)=0 := by
    have e : (1-X)*(X-C z)*q=-((1-X)*(C z-X)*q) := by ring
    rw [e,map_neg,show integral h 1 ((1-X)*(C z-X)*q)=0 from B.reverseInner,neg_zero]
  have middleLaw : SignedThreeLaw a q h u z η := by
    intro F fd
    rw [law F fd] <;> ring
  obtain ⟨hu,_⟩ := actual_right_erasure a0 B.eNeg B.hUnit B.uUnit B.hu.symm B.hz.symm
    hLive middleLaw hScale uScale middle
  have tail : integral z 1 ((1-X)*(X-C h)*q)=0 :=
    right_pair_pays_erasure B.reverseFirst B.reverseSecond
  have tailLaw : SignedThreeLaw a q z u h η := by
    intro F fd
    rw [law F fd] <;> ring
  obtain ⟨_,zuTilt⟩ := actual_right_erasure a0 B.eNeg B.zUnit B.uUnit B.zu.ne' B.hz
    zLive tailLaw zScale uScale tail
  have zhs : q.eval z*q.eval h < 0 := by
    change (q.eval z*(z-u))*(q.eval h*(h-u)) < 0 at zhTilt
    have eq : (q.eval z*(z-u))*(q.eval h*(h-u)) =
        ((z-u)*(h-u))*(q.eval z*q.eval h) := by ring
    rw [eq] at zhTilt
    exact neg_of_mul_neg_right zhTilt
      (mul_pos_of_neg_of_neg (sub_neg.mpr (zh.trans hu)) (sub_neg.mpr hu)).le
  have zus : 0 < q.eval z*q.eval u := by
    change (q.eval z*(z-h))*(q.eval u*(u-h)) < 0 at zuTilt
    have eq : (q.eval z*(z-h))*(q.eval u*(u-h)) =
        ((z-h)*(u-h))*(q.eval z*q.eval u) := by ring
    rw [eq] at zuTilt
    exact pos_of_mul_neg_right zuTilt
      (mul_neg_of_neg_of_pos (sub_neg.mpr zh) (sub_pos.mpr hu)).le
  have hs : q.eval h*q.eval u < 0 := by
    have both := mul_neg_of_neg_of_pos zhs zus
    have eq : (q.eval z*q.eval h)*(q.eval z*q.eval u) =
        (q.eval z)^2*(q.eval h*q.eval u) := by ring
    rw [eq] at both
    exact neg_of_mul_neg_right both (sq_nonneg _)
  exact ⟨zh,hu,zhs,hs⟩

/-- The precise last premise of the frozen cap assembly is now earned
from the actual oriented ports. -/
theorem paidInnerChronologyGate : PaidInnerChronologyGate.{u} := by
  intro L _ _ _ a e u h z r₀ r₁ r₂ B
  exact paid_inner_chronology_of_ports B

/-- Final source endpoint for both literal weak-five SoleInner arms.
There is no unfilled scalar premise and no new real-closure assumption. -/
theorem no_actual_sole_inner {q Z : K[X]} {c : Fin 5 → K}
    (M : Moments q Z c) (S : SoleInner q c) : False :=
  no_actual_sole_inner_of_paid_chronology M S paidInnerChronologyGate

end
end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
