module

public import RKCert.ReviewedNative.WeakFiveInteriorRemainder
public import RKCert.ReviewedNative.CrossedGaussianReflection
public import RKCert.ReviewedNative.CrossedNegativeLocalizer

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Actual weak-five crossed negative tail over the original ordered field

The branch supplies its actual six ordered zeros/marks, global tests,
and two end pairs. The reflection only transports the signed rule and
paid reverse moments, so it does not assume a nonzero value at clock 1. -/
namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

open Polynomial RKCert.ReviewedNative.WeakFive16
open RKCert.ReviewedNative.PositiveRule19
open RKCert.ReviewedNative.CrossedNegativeLocalizer
open RKCert.ReviewedNative.CrossedGaussianEndpointBridge
open RKCert.ReviewedNative.CrossedGaussianSignedAdapter
open RKCert.ReviewedNative.CrossedGaussianReflection
open RKCert.ReviewedNative.FiniteGaussianNodalLift
open RKCert.ReviewedNative.WeakFiveCrossedPositiveTail
open scoped Classical BigOperators

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
set_option maxHeartbeats 1200000

private theorem oriented_no_negative_tail
    {z r h a s u b₀ b₁ : K} {q : K[X]} {μ : K → K}
    (zr : z < r) (rh : r < h) (ha : h < a) (aS : a < s) (su : s < u) (u₁ : u < 1)
    (b₀n : 0 ≤ b₀) (b₁n : 0 ≤ b₁) (tilt : b₁ ≤ b₀)
    (factor : q=density b₀ b₁*((X-C r)*(X-C s)))
    (law₄ : ExactRule (CrossedGaussianSignedAdapter.unitMoment q) (fourMarks z h a u) id μ 9)
    (end₀ : integral 0 u (X*q)=0) (end₁ : integral 0 u (X^2*q)=0) :
    False := by
  let old := fourMarks z h a u
  let t := addMarks old r s
  let B := density b₀ b₁
  let ν := cardinalMass (CrossedGaussianSignedAdapter.unitMoment B) t id
  obtain ⟨count, freshS, freshR, only, _⟩ := crossed_mark_data z r h a s u zr rh ha aS su
  have paid : ExactRule (CrossedGaussianSignedAdapter.unitMoment B) t id ν 11 :=
    six_exact_of_signed_four old r s q B count freshS freshR factor μ law₄
  have mass (x : K) (hx : x ∈ t) : 0 ≤ ν x := by
    apply le_of_lt
    refine six_masses_pos old r s B count freshS freshR
      (density_ne_zero b₀n b₁n) (density_degree _ _) ?_ paid hx
    intro i
    have point := intervalPoint_mem (show (0:K)<1 by norm_num) i
    exact (density_eval_pos b₀n b₁n point.1 point.2).le
  have two := two_below_quarter (t:=t) (μ:=ν) b₁n tilt mass paid
  have small : r < (1:K)/4 := by
    by_contra nr
    have le : (1:K)/4 ≤ r := le_of_not_gt nr
    have eq (x : K) (hx : x ∈ t.filter (fun y => y < (1:K)/4)) : x = z := by
      obtain ⟨xin, lt⟩ := Finset.mem_filter.mp hx
      exact only x xin (lt.trans_le le)
    have atMost : (t.filter (fun x => x < (1:K)/4)).card ≤ 1 :=
      Finset.card_le_one.mpr (fun x hx y hy => (eq x hx).trans (eq y hy).symm)
    omega
  obtain ⟨x, hin, above⟩ := exists_above_seven_eighths (t:=t) (μ:=ν) b₀n b₁n mass paid
  have tail : x ≤ u := by
    have hx : x=r ∨ x=s ∨ x=z ∨ x=h ∨ x=a ∨ x=u := by
      simpa only [t,old,addMarks,fourMarks,Finset.mem_insert,Finset.mem_singleton] using hin
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals linarith only [zr,rh,ha,aS,su]
  have forced := left_pair_forces_quarter b₀n b₁n (above.trans_le tail) u₁ factor end₀ end₁
  exact (not_lt_of_ge small.le) forced

private theorem density_flip (b₀ b₁ : K) :
    flipPoly (density b₀ b₁)=density b₁ b₀ := by
  simp only [flipPoly,density,CrossedNegativeReference.w,add_comp,mul_comp,sub_comp,
    one_comp,X_comp,C_comp,sub_sub_cancel]
  ring

/-- The exact signed packet of the actual two-change chart has no negative
tail, even with a vanishing endpoint coefficient. No reference root,
higher local test, or numerical stage ordering beyond this packet is
assumed. -/
theorem no_actual_crossed_negative_tail {p Z : K[X]} {c : Fin 5 → K} {r s b₀ b₁ : K}
    (T : NegativeTailPacket p Z c r s b₀ b₁) : False := by
  let q := -p
  have f : q=density b₀ b₁*((X-C r)*(X-C s)) := by
    change -p=_
    rw [T.factor,neg_neg] <;> rfl
  obtain ⟨mass, signed⟩ := RKCert.ReviewedNative.WeakFiveCrossedPositiveTail.Moments.exists_signed_four_rule T.moments
  let μ (x : K) := -mass x
  have law : ExactRule (CrossedGaussianSignedAdapter.unitMoment q) (fourMarks (c 4) (c 3) (c 2) (c 1)) id μ 9 := by
    intro H dH
    rw [CrossedGaussianSignedAdapter.unitMoment_apply]
    change integral 0 1 ((FiniteGaussianGridPositivity.unitWeight K*(-p))*H)=_
    have orig := signed H dH
    change integral 0 1 ((FiniteGaussianGridPositivity.unitWeight K*p)*H)=_ at orig
    rw [mul_neg,neg_mul,map_neg,orig]
    simp only [μ,id_eq,neg_mul,Finset.sum_neg_distrib]
  have forward₀ : integral 0 (c 1) (X*q)=0 := by
    simp only [q,mul_neg,map_neg,T.moments.forwardFirst,neg_zero]
  have forward₁ : integral 0 (c 1) (X^2*q)=0 := by
    simp only [q,mul_neg,map_neg,T.moments.forwardSecond,neg_zero]
  have reverse₀ : integral (c 4) 1 ((1-X)*q)=0 := by
    simp only [q,mul_neg,map_neg,T.moments.reverseFirst,neg_zero]
  have reverse₁ : integral (c 4) 1 ((1-X)^2*q)=0 := by
    simp only [q,mul_neg,map_neg,T.moments.reverseSecond,neg_zero]
  by_cases bias : b₁ ≤ b₀
  · exact oriented_no_negative_tail T.order.zr T.order.rh T.order.ha T.order.aS T.order.su T.order.u1
      T.leftNonneg T.rightNonneg bias f law forward₀ forward₁
  · have law' := exact_flip_rule law
    rw [flip_fourMarks] at law'
    have f' := flip_crossed_factor q (density b₀ b₁) r s f
    rw [density_flip] at f'
    have final : flipClock (c 4) < 1 := by
      unfold flipClock
      linarith only [T.order.z0]
    exact oriented_no_negative_tail (flipClock_order T.order.su) (flipClock_order T.order.aS)
      (flipClock_order T.order.ha) (flipClock_order T.order.rh) (flipClock_order T.order.zr) final
      T.rightNonneg T.leftNonneg (le_of_lt (lt_of_not_ge bias)) f' law'
      (flip_forward_first q (c 4) reverse₀) (flip_forward_second q (c 4) reverse₁)

end
end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
