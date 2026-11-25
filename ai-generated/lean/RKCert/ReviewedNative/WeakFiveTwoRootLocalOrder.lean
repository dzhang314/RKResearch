module

public import RKCert.ReviewedNative.WeakFiveSignedTwoRootFactor

import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

/-! # True weak-five windows on the exact two-change profile -/

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

open Polynomial RKCert.ReviewedNative.WeakFive16 RKCert.ReviewedNative.PositiveRule19
open RKCert.ReviewedNative.FiniteOrderedSigns
open scoped Polynomial

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem SignedTwoRootFactor.eval_oriented {p B : K[X]} {r s σ : K}
    (F : SignedTwoRootFactor p B r s σ) (x : K) :
    (p*C σ).eval x = B.eval x*((x-r)*(x-s)) := by
  simpa only [eval_mul, eval_sub, eval_X, eval_C] using congrArg (Polynomial.eval x) F.algebra

private theorem crossing_needs_a_root {p B : K[X]} {r s σ : K} (F : SignedTwoRootFactor p B r s σ)
    {a b : K} (ab : a < b) (au : a ∈ Set.Icc 0 1) (bu : b ∈ Set.Icc 0 1)
    (opp : (p*C σ).eval a*(p*C σ).eval b < 0) :
    (a < r ∧ r < b) ∨ (a < s ∧ s < b) := by
  by_contra same
  have noR : r ≤ a ∨ b ≤ r :=
    (not_and_or.mp (fun h => same (Or.inl h))).imp le_of_not_gt le_of_not_gt
  have noS : s ≤ a ∨ b ≤ s :=
    (not_and_or.mp (fun h => same (Or.inr h))).imp le_of_not_gt le_of_not_gt
  have box (t : K) (blocked : t ≤ a ∨ b ≤ t) : 0 ≤ (a-t)*(b-t) := by
    rcases blocked with early | late
    · exact mul_nonneg (sub_nonneg.mpr early) (sub_nonneg.mpr (early.trans ab.le))
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (ab.le.trans late)) (sub_nonpos.mpr late)
  have alg : (p*C σ).eval a*(p*C σ).eval b =
      (B.eval a*B.eval b)*(((a-r)*(b-r))*((a-s)*(b-s))) := by
    rw [F.eval_oriented a,F.eval_oriented b]
    ring
  rw [alg] at opp
  exact (not_lt_of_ge (mul_nonneg (mul_nonneg (F.nonneg a au) (F.nonneg b bu))
    (mul_nonneg (box r noR) (box s noS)))) opp

private theorem one_root_in_window {p B : K[X]} {r s σ : K} (F : SignedTwoRootFactor p B r s σ)
    {l h : K} (lo : 0 ≤ l) (hi : h ≤ 1) (xs : HasAlternationsOn (p*C σ) (Set.Ioo l h) 1) :
    r ∈ Set.Ioo l h ∨ s ∈ Set.Ioo l h := by
  obtain ⟨x,inc,inner,opp⟩ := finite_alternation_tuple (by decide) xs
  have ic (j : Fin 2) : x j ∈ Set.Icc 0 1 := ⟨lo.trans (inner j).1.le, (inner j).2.le.trans hi⟩
  rcases crossing_needs_a_root F (inc (by decide : (0:Fin 2)<1)) (ic 0) (ic 1) (opp 0) with r0 | s0
  · exact Or.inl ⟨(inner 0).1.trans r0.1,r0.2.trans (inner 1).2⟩
  · exact Or.inr ⟨(inner 0).1.trans s0.1,s0.2.trans (inner 1).2⟩

private theorem both_roots_in_window {p B : K[X]} {r s σ : K} (F : SignedTwoRootFactor p B r s σ)
    {l h : K} (lo : 0 ≤ l) (hi : h ≤ 1) (xs : HasAlternationsOn (p*C σ) (Set.Ioo l h) 2) :
    r ∈ Set.Ioo l h ∧ s ∈ Set.Ioo l h := by
  obtain ⟨x,inc,inner,opp⟩ := finite_alternation_tuple (by decide) xs
  have ic (j : Fin 3) : x j ∈ Set.Icc 0 1 := ⟨lo.trans (inner j).1.le, (inner j).2.le.trans hi⟩
  have a := crossing_needs_a_root F (inc (by decide : (0:Fin 3)<1)) (ic 0) (ic 1) (opp 0)
  have b := crossing_needs_a_root F (inc (by decide : (1:Fin 3)<2)) (ic 1) (ic 2) (opp 1)
  rcases a with ar | as'
  · rcases b with br | bs
    · exact ((ar.2.trans br.1).false).elim
    · exact ⟨⟨(inner 0).1.trans ar.1,ar.2.trans (inner 1).2⟩,
        ⟨(inner 1).1.trans bs.1,bs.2.trans (inner 2).2⟩⟩
  · rcases b with br | bs
    · exact ((as'.2.trans (br.1.trans F.order)).false).elim
    · exact ((as'.2.trans bs.1).false).elim

structure TwoRootWindow (c : Fin 5 → K) (r s : K) : Prop where
  z0 : 0 < c 4
  zr : c 4 < r
  ra : r < c 2
  rh : r < c 3
  as' : c 2 < s
  hs' : c 3 < s
  su : s < c 1
  u1 : c 1 < 1

private theorem sub_x_degree (a : K) : (C a-X : K[X]).natDegree ≤ 1 := by
  rw [← neg_sub, natDegree_neg, natDegree_X_sub_C]

theorem actual_two_root_windows {p B Z : K[X]} {c : Fin 5 → K} {r s σ : K}
    (M : Moments (p*C σ) Z c) (H : AllFourMarksInterior c) (F : SignedTwoRootFactor p B r s σ) :
    TwoRootWindow c r s := by
  have u : MarkInterior c 1 := H 0
  have a : MarkInterior c 2 := H 1
  have h : MarkInterior c 3 := H 2
  have z : MarkInterior c 4 := H 3
  let Q := p*C σ
  obtain ⟨_, sU⟩ := both_roots_in_window F (show (0:K) ≤ 0 from le_rfl) u.2.le (forward_pair_inside M u.1)
  obtain ⟨rZ, _⟩ := both_roots_in_window F z.1.le le_rfl (reverse_pair_inside M z.2)
  have au : c 2 < c 1 := by
    by_contra! ua
    have distinct : c 1 ≠ c 2 := fun eq => (by decide : (1:Fin 5) ≠ 2) (M.clockSimple eq)
    have uu : c 1 < c 2 := lt_of_le_of_ne ua distinct
    have dif : HasAlternationsOn Q (Set.Ioo (c 1) (c 2)) 1 :=
      variation_of_one_test uu M.qNonzero M.qDegree
        (natDegree_mul_le_of_le natDegree_X.le (natDegree_X_sub_C _).le) (by
          intro x hx
          simp only [eval_mul, eval_sub, eval_X, eval_C]
          exact mul_pos (u.1.trans hx.1) (sub_pos.mpr hx.1))
        (forward_genuine_difference M)
    have impossible := one_root_in_window F u.1.le a.2.le dif
    rcases impossible with rr | ss
    · exact (not_lt_of_ge ((F.order.trans sU.2).le)) rr.1
    · exact (not_lt_of_ge sU.2.le) ss.1
  have zh : c 4 < c 3 := by
    by_contra! hz
    have distinct : c 3 ≠ c 4 := fun eq => (by decide : (3:Fin 5) ≠ 4) (M.clockSimple eq)
    have zz : c 3 < c 4 := lt_of_le_of_ne hz distinct
    have dif : HasAlternationsOn Q (Set.Ioo (c 3) (c 4)) 1 :=
      variation_of_one_test zz M.qNonzero M.qDegree
        (natDegree_mul_le_of_le (unit_right_weight_degree (K := K)).le (sub_x_degree _)) (by
          intro x hx
          simp only [eval_mul, eval_sub, eval_one, eval_X, eval_C]
          exact mul_pos (sub_pos.mpr (hx.2.trans z.2)) (sub_pos.mpr hx.2))
        (reverse_genuine_difference M)
    rcases one_root_in_window F h.1.le z.2.le dif with rr | ss
    · exact (not_lt_of_ge rZ.1.le) rr.2
    · exact (not_lt_of_ge ((rZ.1.trans F.order).le)) ss.2
  let U := X*(C (c 1)-X)
  let V := (1-X)*(X-C (c 4))
  have Upos {l h : K} (l0 : 0 ≤ l) (hu : h ≤ c 1) :
      ∀ x ∈ Set.Ioo l h, 0 < U.eval x := by
    intro x hx
    simp only [U, eval_mul, eval_sub, eval_X, eval_C]
    exact mul_pos (l0.trans_lt hx.1) (sub_pos.mpr (hx.2.trans_le hu))
  have Vpos {l h : K} (zl : c 4 ≤ l) (h1 : h ≤ 1) :
      ∀ x ∈ Set.Ioo l h, 0 < V.eval x := by
    intro x hx
    simp only [V, eval_mul, eval_sub, eval_X, eval_C, eval_one]
    exact mul_pos (sub_pos.mpr (hx.2.trans_le h1)) (sub_pos.mpr (zl.trans_lt hx.1))
  have Ud : U.natDegree ≤ 2 := natDegree_mul_le_of_le natDegree_X.le (sub_x_degree _)
  have Vd : V.natDegree ≤ 2 := natDegree_mul_le_of_le (unit_right_weight_degree (K:=K)).le
    (natDegree_X_sub_C _).le
  have zl (t v : K) :
      integral t v (U*Q) = -integral t v (X*(X-C (c 1))*Q) := by
    rw [show U*Q = -(X*(X-C (c 1))*Q) by dsimp only [U]; ring, map_neg]
  have zr (t v : K) :
      integral t v (V*Q) = -integral t v ((1-X)*(C (c 4)-X)*Q) := by
    rw [show V*Q = -((1-X)*(C (c 4)-X)*Q) by dsimp only [V]; ring, map_neg]
  have aLeft := variation_of_one_test a.1 M.qNonzero M.qDegree Ud
    (Upos le_rfl au.le) (by rw [zl, M.forwardInner, neg_zero])
  have aRight := variation_of_one_test au M.qNonzero M.qDegree Ud
    (Upos a.1.le le_rfl) (by rw [zl, exact_integral_reverse _ (c 1) (c 2),forward_genuine_difference M,
      neg_zero,neg_zero])
  have hLeft := variation_of_one_test zh M.qNonzero M.qDegree Vd
    (Vpos le_rfl h.2.le) (by rw [zr, exact_integral_reverse _ (c 3) (c 4),reverse_genuine_difference M,
      neg_zero,neg_zero])
  have hRight := variation_of_one_test h.2 M.qNonzero M.qDegree Vd
    (Vpos zh.le le_rfl) (by rw [zr, M.reverseInner,neg_zero])
  have ra := (one_root_in_window F (show (0:K) ≤ 0 from le_rfl) a.2.le aLeft).elim
    (fun rr => rr.2) (fun ss => F.order.trans ss.2)
  have as' := (one_root_in_window F a.1.le u.2.le aRight).elim
    (fun rr => rr.1.trans F.order) (fun ss => ss.1)
  have rh := (one_root_in_window F z.1.le h.2.le hLeft).elim
    (fun rr => rr.2) (fun ss => F.order.trans ss.2)
  have hs' := (one_root_in_window F h.1.le le_rfl hRight).elim
    (fun rr => rr.1.trans F.order) (fun ss => ss.1)
  exact ⟨z.1,rZ.1,ra,rh,as',hs',sU.2,u.2⟩

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
