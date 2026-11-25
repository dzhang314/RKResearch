module

public import RKCert.ReviewedNative.WeakFiveTwoRootCrossing
public import RKCert.ReviewedNative.ERKOrder16WeakFiveCrossedPositiveTailOrdered

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # The genuine crossed positive-tail endpoint consumes the two-change phase

This leaves the affine-residual three-change sector or the exact negative
tail. The latter earns its two nonnegative endpoint coefficients from the
actual normalized quadratic; no auxiliary sign test is used as an input.
-/

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

open Polynomial RKCert.ReviewedNative.WeakFive16 RKCert.ReviewedNative.PositiveRule19
open RKCert.ReviewedNative.FiniteOrderedSigns RKCert.ReviewedNative.OrderedRootGapSaturation
open RKCert.ReviewedNative.CrossedPositiveTailRoots
open RKCert.ReviewedNative.WeakFiveCrossedPositiveTail
open scoped Polynomial BigOperators

universe u
variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

noncomputable section

def negativeQuadratic (b₀ b₁ : K) : K[X] := X*(1-X)+C b₀*(1-X)+C b₁*X

theorem negativeQuadratic_eval_pos {b₀ b₁ x : K} (l : 0≤b₀) (h : 0≤b₁)
    (hx : x ∈ Set.Ioo (0:K) 1) : 0 < (negativeQuadratic b₀ b₁).eval x := by
  simp only [negativeQuadratic, eval_add,eval_mul,eval_C,eval_X,eval_sub,eval_one]
  exact add_pos_of_pos_of_nonneg
    (add_pos_of_pos_of_nonneg (mul_pos hx.1 (sub_pos.mpr hx.2)) (mul_nonneg l (sub_nonneg.mpr hx.2.le)))
    (mul_nonneg h hx.1.le)

theorem quadratic_of_minus_one_leading {B : K[X]} (degree : B.natDegree = 2) (lc : B.leadingCoeff = -1) :
    B = negativeQuadratic (B.eval 0) (B.eval 1) := by
  have top : B.coeff 2 = -1 := by rw [← degree, coeff_natDegree, lc]
  have rep : B = C (B.coeff 0) + C (B.coeff 1)*X-X^2 := by
    nth_rewrite 1 [B.as_sum_range' 3 (by omega)]
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,top,
      ← C_mul_X_pow_eq_monomial,pow_zero,pow_one,mul_one,C_neg,C_1,neg_mul,one_mul]
    ring
  have e0 : B.eval 0 = B.coeff 0 := by
    rw [← coeff_zero_eq_eval_zero]
  have e1 : B.eval 1 = B.coeff 0 + B.coeff 1 - 1 := by
    simpa using congrArg (Polynomial.eval (1:K)) rep
  calc B = C (B.coeff 0) + C (B.coeff 1)*X-X^2 := rep
       _ = negativeQuadratic (B.eval 0) (B.eval 1) := by
        simp only [negativeQuadratic, e0,e1, map_add,map_sub,map_one]
        ring

/-- Orientation-neutral endpoint; all seven inequalities are paid by the
literal chart and the actual two-change polynomial, not by guessed marks. -/
structure ActualCrossedOrder (c : Fin 5 → K) (r s : K) : Prop where
  z0 : 0 < c 4
  zr : c 4 < r
  rh : r < c 3
  ha : c 3 < c 2
  aS : c 2 < s
  su : s < c 1
  u1 : c 1 < 1

structure NegativeTailPacket (p Z : K[X]) (c : Fin 5 → K) (r s b₀ b₁ : K) : Prop where
  moments : Moments p Z c
  monic : p.Monic
  degree : p.natDegree = 4
  order : ActualCrossedOrder c r s
  leftNonneg : 0 ≤ b₀
  rightNonneg : 0 ≤ b₁
  factor : p = -(negativeQuadratic b₀ b₁*((X-C r)*(X-C s)))

private theorem positive_site_values {p B Z : K[X]} {r s : K} {c : Fin 5 → K} (M : Moments p Z c)
    (G : AllFourMarksInterior c) (F : SignedTwoRootFactor p B r s 1) (H : ActualCrossedOrder c r s) :
    0 < p.eval (c 4) ∧ p.eval (c 3) < 0 ∧ p.eval (c 2) < 0 ∧ 0 < p.eval (c 1) := by
  have ep (x : K) : p.eval x = B.eval x*((x-r)*(x-s)) := by
    simpa only [map_one,mul_one] using F.eval_oriented x
  have bp (i : Fin 4) : 0 < B.eval (c i.succ) := by
    have le := F.nonneg _ ⟨(G i).1.le,(G i).2.le⟩
    apply lt_of_le_of_ne le
    intro bad
    have z := ep (c i.succ)
    rw [← bad,zero_mul] at z
    exact (M.active i.succ).2 z
  constructor
  · rw [ep]
    exact mul_pos (bp 3) (mul_pos_of_neg_of_neg (sub_neg.mpr H.zr) (sub_neg.mpr (H.zr.trans F.order)))
  constructor
  · rw [ep]
    exact mul_neg_of_pos_of_neg (bp 2) (mul_neg_of_pos_of_neg (sub_pos.mpr H.rh)
      (sub_neg.mpr (H.ha.trans H.aS)))
  constructor
  · rw [ep]
    exact mul_neg_of_pos_of_neg (bp 1) (mul_neg_of_pos_of_neg (sub_pos.mpr (H.rh.trans H.ha))
      (sub_neg.mpr H.aS))
  · rw [ep]
    exact mul_pos (bp 0) (mul_pos (sub_pos.mpr (F.order.trans H.su)) (sub_pos.mpr H.su))

/-- The ordered positive-tail consumer charges the six actual local
equations plus the original guarded signed law. We supply its last missing
phase from the classified two-change factor and genuine difference windows. -/
theorem two_change_branch_is_negative {p Z : K[X]} {c : Fin 5 → K}
    (M : Moments p Z c) (mono : p.Monic) (deg : p.natDegree = 4)
    (unit : AllFourMarksInterior c) (g : GapComplete p)
    (two : HasAlternationsOn p (Set.Ioo (0:K) 1) 2)
    (noThree : ¬ HasAlternationsOn p (Set.Ioo (0:K) 1) 3) :
    ∃ r s b₀ b₁ : K, NegativeTailPacket p Z c r s b₀ b₁ := by
  obtain ⟨B,r,s,σ,F⟩ := signed_two_root_factor mono deg g two noThree
  have sn : σ ≠ 0 := by
    rcases F.sign with h | h <;> rw [h] <;> simp
  have N := moments_scale_nonzero M sn
  have H := actual_two_root_windows N unit F
  have ha := crossed_inner_order_of_two_root_factor N F H
  have ord : ActualCrossedOrder c r s := ⟨H.z0,H.zr,H.rh,ha,H.as',H.su,H.u1⟩
  rcases F.sign with positive | negative
  · subst σ
    obtain ⟨zp,hn,an,up⟩ := positive_site_values M unit F ord
    have ph : CrossedSignPhase p (c 4) (c 3) (c 2) (c 1) :=
      ⟨ord.z0,ord.zr.trans ord.rh,ord.ha,ord.aS.trans ord.su,ord.u1,zp,hn,an,up,noThree⟩
    have eig : monicProfile p = p := by rw [monicProfile, mono.leadingCoeff, inv_one, C_1, mul_one]
    exact (no_actual_crossed_positive_tail_ordered M deg (by rwa [eig])).elim
  · subst σ
    have sh := quadratic_of_minus_one_leading F.degree F.leading
    have neg : p = -(B*((X-C r)*(X-C s))) := by
      have eq := F.algebra
      rw [map_neg, map_one, mul_neg, mul_one] at eq
      rw [← eq, neg_neg]
    refine ⟨r,s,B.eval 0,B.eval 1,⟨M,mono,deg,ord,F.nonneg 0 ⟨le_rfl,zero_le_one⟩,
      F.nonneg 1 ⟨zero_le_one,le_rfl⟩,?_⟩⟩
    calc p = -(B*((X-C r)*(X-C s))) := neg
         _ = _ := congrArg (fun v => -(v*((X-C r)*(X-C s)))) sh

/-- The only possible interior shapes after all currently attached checked
scalar consumers have fired. The exterior endpoints are handled separately. -/
theorem actual_interior_remainder {q Z : K[X]} {c : Fin 5 → K} (M : Moments q Z c)
    (marks : AllFourMarksInterior c) :
    (∃ E : OrderedExtension K, ∃ (r : Fin 3 → E.carrier) (e : E.carrier),
      ThreeChangeLayout (q.map E.embed) r e) ∨
    (∃ E : OrderedExtension K, ∃ (r s b₀ b₁ : E.carrier),
      NegativeTailPacket (monicProfile (q.map E.embed)) (Z.map E.embed)
        (fun i => E.embed (c i)) r s b₀ b₁) := by
  rcases all_interior_root_modes M marks with three | stable
  · exact Or.inl three
  · right
    obtain ⟨E,g⟩ := self_gap_complete_extension q
    let Q := q.map E.embed
    let p := monicProfile Q
    have N := moments_along_field E.embed M
    have nz : Q ≠ 0 := N.qNonzero
    have cn : Q.leadingCoeff⁻¹ ≠ 0 := inv_ne_zero (leadingCoeff_ne_zero.mpr nz)
    have Np : Moments p (Z.map E.embed) (fun i => E.embed (c i)) := moments_scale_nonzero N cn
    have gp : GapComplete p := g.scale cn
    have mono : p.Monic := monicProfile_monic Q nz
    have ng : ¬ HasAlternationsOn p (Set.Ioo (0:E.carrier) 1) 3 :=
      fun x => stable E ((alternations_scale_unit_iff cn).mp x)
    have two : HasAlternationsOn p (Set.Ioo (0:E.carrier) 1) 2 :=
      Np.unit_alternations_of_exterior_count.mono (fun _ h => h) (by omega)
    obtain ⟨r,s,b₀,b₁,H⟩ := two_change_branch_is_negative Np mono
      Np.natDegree_eq_four_of_full_packet (map_interior_marks E marks) gp two ng
    exact ⟨E,r,s,b₀,b₁,H⟩

end

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
