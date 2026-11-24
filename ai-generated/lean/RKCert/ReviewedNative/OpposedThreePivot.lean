module

public import RKCert.ReviewedNative.PositiveIntervalGrid19
import RKCert.ReviewedNative.OneWeightOrderedSigns
import RKCert.ReviewedNative.OrderedAlternationDegree
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Opposed 3+2+1 polynomial moments at three interior pivots

The labels are chronological, not numerical. Only the one-weight grid,
strictly separated open-window addition, and the degree ceiling are used.
-/
namespace RKCert.ReviewedNative.FiniteOrderedSigns

open Polynomial RKCert.ReviewedNative.PositiveRule19
noncomputable section

variable {K : Type*} [Field K]

section Input
variable [CharZero K]

/-- Two opposed families of local moments. The base weights may differ. -/
structure OpposedThreePivotMoments (P U V : K[X]) (a b c : K) : Prop where
  leftFirst : ∀ k : Fin 3, integral 0 a (U*P*X^k.val)=0
  leftSecond : ∀ k : Fin 2, integral 0 b (U*(X-C a)*P*X^k.val)=0
  leftThird : integral 0 c (U*(X-C a)*(X-C b)*P)=0
  rightFirst : ∀ k : Fin 3, integral c 1 (V*P*X^k.val)=0
  rightSecond : ∀ k : Fin 2, integral b 1 (V*(X-C c)*P*X^k.val)=0
  rightThird : integral a 1 (V*(X-C c)*(X-C b)*P)=0

end Input

variable [LinearOrder K] [IsStrictOrderedRing K]

private theorem shiftTwo {l r : K} {M P : K[X]}
    (paid : ∀ j : Fin 3, integral l r (M*P*X^j.val)=0) (t : K) (k : Fin 2) :
    integral l r (M*(X-C t)*P*X^k.val)=0 := by
  have hk := k.isLt
  have p0 : integral l r (M*P*X^k.val)=0 := paid ⟨k.val,by omega⟩
  have p1 : integral l r (M*P*X^(k.val+1))=0 := paid ⟨k.val+1,by omega⟩
  rw [show M*(X-C t)*P*X^k.val = M*P*X^(k.val+1) - t • (M*P*X^k.val) by
      rw [pow_succ,smul_eq_C_mul]
      ring,
    map_sub,map_smul,p1,p0,smul_zero,sub_zero]

private theorem betweenLeft {o l r : K} {B : K[X]}
    (hl : integral o l B=0) (hr : integral o r B=0) : integral l r B=0 := by
  simp only [integral_apply] at hl hr ⊢
  exact sub_eq_zero.mpr ((sub_eq_zero.mp hr).trans (sub_eq_zero.mp hl).symm)

private theorem betweenRight {o l r : K} {B : K[X]}
    (hl : integral l o B=0) (hr : integral r o B=0) : integral l r B=0 := by
  simp only [integral_apply] at hl hr ⊢
  exact sub_eq_zero.mpr ((sub_eq_zero.mp hr).symm.trans (sub_eq_zero.mp hl))

private theorem twoOnLinearMask {l r t : K} {M P : K[X]}
    (pn : P≠0) (lr : l<r) (l0 : 0≤l) (r1 : r≤1)
    (pos : ∀ x∈Set.Ioo (0:K) 1, 0<M.eval x)
    (budget : M.natDegree+P.natDegree+2≤19) (sep : r≤t ∨ t≤l)
    (paid : ∀ k : Fin 2, integral l r (M*(X-C t)*P*X^k.val)=0) :
    HasAlternationsOn P (Set.Ioo l r) 2 := by
  have psmall : P.natDegree<19 := by omega
  have d : (M*(X-C t)).natDegree+P.natDegree+(2-1)≤19 := by
    have h := natDegree_mul_le (p:=M) (q:=X-C t)
    rw [natDegree_X_sub_C] at h
    omega
  have inside (x : K) (hx : x∈Set.Ioo l r) : x∈Set.Ioo (0:K) 1 :=
    ⟨l0.trans_lt hx.1,hx.2.trans_le r1⟩
  rcases sep with left | right
  · refine HasAlternationsOn.of_grid lr (grid_variation_of_positive_moments
      (U := -(M*(X-C t))) (m := 2) lr pn psmall
      (by simpa only [natDegree_neg] using d) ?_ ?_)
    · intro x hx
      simp only [eval_neg,eval_mul,eval_sub,eval_X,eval_C]
      exact neg_pos.mpr (mul_neg_of_pos_of_neg (pos x (inside x hx))
        (sub_neg.mpr (hx.2.trans_le left)))
    · intro k
      simp only [neg_mul,map_neg,paid k,neg_zero]
  · refine HasAlternationsOn.of_grid lr (grid_variation_of_positive_moments
      (U := M*(X-C t)) (m := 2) lr pn psmall d ?_ paid)
    intro x hx
    simp only [eval_mul,eval_sub,eval_X,eval_C]
    exact mul_pos (pos x (inside x hx)) (sub_pos.mpr (right.trans_lt hx.1))

private theorem oneOnDoubleMask {l r t w : K} {M P : K[X]}
    (pn : P≠0) (lr : l<r) (l0 : 0≤l) (r1 : r≤1)
    (pos : ∀ x∈Set.Ioo (0:K) 1, 0<M.eval x)
    (budget : M.natDegree+P.natDegree+2≤19)
    (sep : (r≤t ∧ r≤w) ∨ (t≤l ∧ w≤l))
    (paid : integral l r (M*(X-C t)*(X-C w)*P)=0) :
    HasAlternationsOn P (Set.Ioo l r) 1 := by
  have psmall : P.natDegree<19 := by omega
  have d : (M*(X-C t)*(X-C w)).natDegree+P.natDegree+(1-1)≤19 := by
    have h₁ := natDegree_mul_le (p:=M) (q:=X-C t)
    have h₂ := natDegree_mul_le (p:=M*(X-C t)) (q:=X-C w)
    rw [natDegree_X_sub_C] at h₁ h₂
    omega
  refine HasAlternationsOn.of_grid lr (grid_variation_of_positive_moments
    (U := M*(X-C t)*(X-C w)) (m := 1) lr pn psmall d ?_ ?_)
  · intro x hx
    have mp := pos x ⟨l0.trans_lt hx.1,hx.2.trans_le r1⟩
    simp only [eval_mul,eval_sub,eval_X,eval_C]
    rcases sep with ⟨lt, lw⟩ | ⟨tr, wr⟩
    · exact mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg mp (sub_neg.mpr (hx.2.trans_le lt)))
        (sub_neg.mpr (hx.2.trans_le lw))
    · exact mul_pos (mul_pos mp (sub_pos.mpr (tr.trans_lt hx.1)))
        (sub_pos.mpr (wr.trans_lt hx.1))
  · intro k
    have hk : k.val=0 := by have h := k.isLt; omega
    simpa only [hk,pow_zero,mul_one] using paid

/-- Opposed three-, two-, and one-moment windows force degree at least
six at three distinct interior pivots, in any numerical order. -/
theorem OpposedThreePivotMoments.six_le_natDegree {P U V : K[X]} {a b c : K}
    (H : OpposedThreePivotMoments P U V a b c) (pn : P≠0)
    (ha : a∈Set.Ioo (0:K) 1) (hb : b∈Set.Ioo (0:K) 1) (hc : c∈Set.Ioo (0:K) 1)
    (abNe : a≠b) (acNe : a≠c) (bcNe : b≠c)
    (uPos : ∀ x∈Set.Ioo (0:K) 1, 0<U.eval x)
    (vPos : ∀ x∈Set.Ioo (0:K) 1, 0<V.eval x)
    (uBudget : U.natDegree+P.natDegree+2≤19) (vBudget : V.natDegree+P.natDegree+2≤19) :
    6≤P.natDegree := by
  have psmall : P.natDegree<19 := by omega
  have L1 : HasAlternationsOn P (Set.Ioo 0 a) 3 := by
    refine HasAlternationsOn.of_grid ha.1 (grid_variation_of_positive_moments
      (U := U) (m := 3) ha.1 pn psmall uBudget ?_ H.leftFirst)
    intro x hx
    exact uPos x ⟨hx.1,hx.2.trans ha.2⟩
  have R1 : HasAlternationsOn P (Set.Ioo c 1) 3 := by
    refine HasAlternationsOn.of_grid hc.2 (grid_variation_of_positive_moments
      (U := V) (m := 3) hc.2 pn psmall vBudget ?_ H.rightFirst)
    intro x hx
    exact vPos x ⟨hc.1.trans hx.1,hx.2⟩
  have L2a (k : Fin 2) : integral 0 a (U*(X-C a)*P*X^k.val)=0 :=
    shiftTwo H.leftFirst a k
  have R2c (k : Fin 2) : integral c 1 (V*(X-C c)*P*X^k.val)=0 :=
    shiftTwo H.rightFirst c k
  rcases lt_or_gt_of_ne acNe with ac | ca
  · -- a < c: the first windows alone are disjoint (3+3).
    exact (L1.add_open R1 ha.1.le ac.le hc.2.le).le_natDegree
  · rcases lt_or_gt_of_ne bcNe with bc | cb
    · -- b < c < a: two second windows and the first right window (2+2+3).
      have A : HasAlternationsOn P (Set.Ioo 0 b) 2 :=
        twoOnLinearMask pn hb.1 le_rfl hb.2.le uPos uBudget
          (Or.inl (bc.trans ca).le) H.leftSecond
      have B : HasAlternationsOn P (Set.Ioo b c) 2 :=
        twoOnLinearMask (t:=c) pn bc hb.1.le hc.2.le vPos vBudget (Or.inl le_rfl)
          (fun k => betweenRight (H.rightSecond k) (R2c k))
      have AB := A.add_open B hb.1.le le_rfl bc.le
      have d := (AB.add_open R1 hc.1.le le_rfl hc.2.le).le_natDegree
      omega
    · rcases lt_or_gt_of_ne abNe with ab | ba
      · -- c < a < b: first left and two second windows (3+2+2).
        have A : HasAlternationsOn P (Set.Ioo a b) 2 :=
          twoOnLinearMask (t:=a) pn ab ha.1.le hb.2.le uPos uBudget (Or.inr le_rfl)
            (fun k => betweenLeft (L2a k) (H.leftSecond k))
        have B : HasAlternationsOn P (Set.Ioo b 1) 2 :=
          twoOnLinearMask pn hb.2 hb.1.le le_rfl vPos vBudget (Or.inr cb.le) H.rightSecond
        have LA := L1.add_open A ha.1.le le_rfl ab.le
        have d := (LA.add_open B hb.1.le le_rfl hb.2.le).le_natDegree
        omega
      · -- c < b < a: the second windows are inward, with both third tails (1+2+2+1).
        have A : HasAlternationsOn P (Set.Ioo 0 c) 1 :=
          oneOnDoubleMask (t:=a) (w:=b) pn hc.1 le_rfl hc.2.le uPos uBudget
            (Or.inl ⟨ca.le,cb.le⟩) H.leftThird
        have B : HasAlternationsOn P (Set.Ioo c b) 2 :=
          twoOnLinearMask (t:=c) pn cb hc.1.le hb.2.le vPos vBudget (Or.inr le_rfl)
            (fun k => betweenRight (R2c k) (H.rightSecond k))
        have C' : HasAlternationsOn P (Set.Ioo b a) 2 :=
          twoOnLinearMask (t:=a) pn ba hb.1.le ha.2.le uPos uBudget (Or.inl le_rfl)
            (fun k => betweenLeft (H.leftSecond k) (L2a k))
        have D : HasAlternationsOn P (Set.Ioo a 1) 1 :=
          oneOnDoubleMask (t:=c) (w:=b) pn ha.2 ha.1.le le_rfl vPos vBudget
            (Or.inr ⟨ca.le,ba.le⟩) H.rightThird
        have AB := A.add_open B hc.1.le le_rfl cb.le
        have ABC := AB.add_open C' hb.1.le le_rfl ba.le
        exact (ABC.add_open D ha.1.le le_rfl ha.2.le).le_natDegree

end
end RKCert.ReviewedNative.FiniteOrderedSigns
