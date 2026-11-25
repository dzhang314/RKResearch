module

public import RKCert.ReviewedNative.WeakFiveOneExteriorClassifier

import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Geometric data paid by the literal single-exterior alternatives -/

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

open Polynomial RKCert.ReviewedNative.WeakFive16 RKCert.ReviewedNative.PositiveRule19
open RKCert.ReviewedNative.FiniteOrderedSigns RKCert.ReviewedNative.FiniteRootSeparator
open RKCert.ReviewedNative.OrderedRootGapSaturation RKCert.ReviewedNative.OrderedPolynomialSignStrips
open scoped Polynomial

universe u
variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem variation_of_one_test {q W : K[X]} {l r : K}
    (lr : l < r) (qn : q ≠ 0) (qd : q.natDegree ≤ 4) (wd : W.natDegree ≤ 2)
    (pos : ∀ x ∈ Set.Ioo l r, 0 < W.eval x) (paid : integral l r (W*q) = 0) :
    HasAlternationsOn q (Set.Ioo l r) 1 := by
  apply HasAlternationsOn.of_grid lr
  apply grid_variation_of_positive_moments lr qn (qd.trans_lt (by decide)) (by omega) pos
  intro i
  have iz : i.val = 0 := Nat.lt_one_iff.mp i.isLt
  simpa only [iz, pow_zero, mul_one] using paid

theorem paid_unit_three_of_mark_exterior {q Z : K[X]} {c : Fin 5 → K} (M : Moments q Z c)
    {i : Fin 5} (ni : i ≠ 0) (side : c i < 0 ∨ 1 < c i) :
    HasAlternationsOn q (Set.Ioo (0 : K) 1) 3 := by
  classical
  have hm : i ∈ exteriorMarkedClocks c := by simp [exteriorMarkedClocks, ni, side]
  have hc : 0 < (exteriorMarkedClocks c).card := Finset.card_pos.mpr ⟨i, hm⟩
  exact M.unit_alternations_of_exterior_count.mono (fun _ h => h) (by omega)

theorem left_inner_exterior_alternation {q Z : K[X]} {c : Fin 5 → K} (M : Moments q Z c)
    (a : c 2 < 0) (u : 0 < c 1) : HasAlternationsOn q (Set.Ioo (c 2) 0) 1 := by
  have deg : (X*(X-C (c 1))).natDegree ≤ 2 := natDegree_mul_le_of_le natDegree_X.le
    (natDegree_X_sub_C _).le
  refine variation_of_one_test a M.qNonzero M.qDegree deg ?_ ?_
  · intro x hx
    simp only [eval_mul, eval_sub, eval_X, eval_C]
    exact mul_pos_of_neg_of_neg hx.2 (sub_neg.mpr (hx.2.trans u))
  · rw [exact_integral_reverse _ 0 (c 2), M.forwardInner, neg_zero]

theorem right_inner_exterior_alternation {q Z : K[X]} {c : Fin 5 → K} (M : Moments q Z c)
    (h : 1 < c 3) (z : c 4 < 1) : HasAlternationsOn q (Set.Ioo 1 (c 3)) 1 := by
  have unitD : (1-X : K[X]).natDegree ≤ 1 := (unit_right_weight_degree (K := K)).le
  have stopD : (C (c 4)-X : K[X]).natDegree ≤ 1 := by
    rw [← neg_sub, natDegree_neg, natDegree_X_sub_C]
  refine variation_of_one_test h M.qNonzero M.qDegree (natDegree_mul_le_of_le unitD stopD) ?_ ?_
  · intro x hx
    simp only [eval_mul, eval_sub, eval_one, eval_X, eval_C]
    exact mul_pos_of_neg_of_neg (sub_neg.mpr hx.1) (sub_neg.mpr (z.trans hx.1))
  · rw [exact_integral_reverse _ (c 3) 1, M.reverseInner, neg_zero]

theorem inner_left_outers_overlap {q Z : K[X]} {c : Fin 5 → K} (M : Moments q Z c)
    (a : c 2 < 0) (u : MarkInterior c 1) (z : MarkInterior c 4) : c 4 < c 1 := by
  by_contra! not
  have four := (forward_pair_inside M u.1).add_open (reverse_pair_inside M z.2) u.1.le not z.2.le
  have five := (left_inner_exterior_alternation M a u.1).add_open four a.le le_rfl zero_le_one
  have cap := five.le_natDegree
  have up := M.qDegree
  omega

theorem inner_right_outers_overlap {q Z : K[X]} {c : Fin 5 → K} (M : Moments q Z c)
    (h : 1 < c 3) (u : MarkInterior c 1) (z : MarkInterior c 4) : c 4 < c 1 := by
  by_contra! not
  have four := (forward_pair_inside M u.1).add_open (reverse_pair_inside M z.2) u.1.le not z.2.le
  have five := four.add_open (right_inner_exterior_alternation M h z.2) zero_le_one le_rfl h.le
  have cap := five.le_natDegree
  have up := M.qDegree
  omega

theorem outer_left_u_lt_h {q Z : K[X]} {c : Fin 5 → K} (M : Moments q Z c)
    (z : c 4 < 0) (u : MarkInterior c 1) (h : MarkInterior c 3) : c 1 < c 3 := by
  by_contra! wrong
  obtain ⟨A, B, D, A0, B0, D0, eq⟩ := moments_primitive_balance M
  have neg1 := mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos z h.1) B0
  have p := mul_nonpos_of_nonpos_of_nonneg
    (mul_neg_of_neg_of_pos (sub_neg.mpr u.2) (sub_pos.mpr (z.trans u.1))).le (sub_nonneg.mpr wrong)
  have neg2 := mul_nonpos_of_nonpos_of_nonneg p D0.le
  have rhs := add_nonpos neg1.le neg2
  rw [← eq] at rhs
  exact (not_lt_of_ge rhs) (mul_pos u.1 A0)

theorem outer_right_a_lt_z {q Z : K[X]} {c : Fin 5 → K} (M : Moments q Z c)
    (u : 1 < c 1) (a : MarkInterior c 2) (z : MarkInterior c 4) : c 2 < c 4 := by
  by_contra! wrong
  obtain ⟨A, B, D, A0, B0, D0, eq⟩ := reflected_moments_primitive_balance M
  have neg1 := mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (sub_neg.mpr u) (sub_pos.mpr a.2)) B0
  have leftP : ((1-c 4)-1)*((1-c 4)-(1-c 1)) < 0 := by
    apply mul_neg_of_neg_of_pos <;> linarith only [z.1, z.2, u]
  have rightP : 0 ≤ (1-c 4)-(1-c 2) := by linarith only [wrong]
  have neg2 := mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg leftP.le rightP) D0.le
  have rhs := add_nonpos neg1.le neg2
  rw [← eq] at rhs
  exact (not_lt_of_ge rhs) (mul_pos (sub_pos.mpr z.2) A0)

/-- Exact shape from three unit gaps and one disjoint exterior gap.
The same extension supplies the original chart and all four actual roots. -/
structure ExteriorRootLayout (p : K[X]) (r : Fin 3 → K) (e l h : K) : Prop where
  sorted : StrictMono r
  unit : ∀ j, r j ∈ Set.Ioo 0 1
  edge : e ∈ Set.Ioo l h
  factor : p = C p.leadingCoeff * ((X-C e)*indexedHull r Finset.univ)

theorem three_unit_and_external_gap {q : K[X]} (qd : q.natDegree ≤ 4) {l h : K}
    (external : h ≤ 0 ∨ 1 ≤ l)
    (unit : HasAlternationsOn q (Set.Ioo (0 : K) 1) 3)
    (out : HasAlternationsOn q (Set.Ioo l h) 1) :
    ∃ E : OrderedExtension K, ∃ (r : Fin 3 → E.carrier) (e : E.carrier),
      ExteriorRootLayout (q.map E.embed) r e (E.embed l) (E.embed h) := by
  classical
  obtain ⟨x, xo, xi, xp⟩ := finite_alternation_tuple (by decide) out
  obtain ⟨E, r, ro, ri, rr⟩ := roots_of_paid_unit_alternations (by decide) unit
  have pair : Opposite ((q.map E.embed).eval (E.embed (x 0))) ((q.map E.embed).eval (E.embed (x 1))) := by
    apply mul_neg_iff.mp
    rw [Polynomial.eval_map_apply, Polynomial.eval_map_apply, ← map_mul, ← map_zero E.embed]
    exact E.mono (xp 0)
  obtain ⟨F, e, lo, hi, eroot⟩ := RKCert.ReviewedNative.OrderedSingleGapRoot.singleGapFactory
    E.carrier (q.map E.embed) _ _ (E.mono (xo (by decide : (0 : Fin 2) < 1))) pair
  let G := followedBy E F
  let v : Fin 3 → G.carrier := F.embed ∘ r
  have xo0 := (xi 0).1
  have xo1 := (xi 1).2
  have edge : e ∈ Set.Ioo (G.embed l) (G.embed h) :=
    ⟨(G.mono xo0).trans lo, hi.trans (G.mono xo1)⟩
  have ord : StrictMono v := F.mono.comp ro
  have U (j : Fin 3) : v j ∈ Set.Ioo 0 1 :=
    ⟨by simpa only [v, Function.comp_apply, map_zero] using F.mono (ri j).1,
     by simpa only [v, Function.comp_apply, map_one] using F.mono (ri j).2⟩
  have nz (j : Fin 3) : e ≠ v j := by
    rcases external with left | right
    · have b : G.embed h ≤ 0 := by simpa only [map_zero] using G.mono.monotone left
      exact ((edge.2.trans_le b).trans (U j).1).ne
    · have b : 1 ≤ G.embed l := by simpa only [map_one] using G.mono.monotone right
      exact (((U j).2.trans_le b).trans edge.1).ne'
  have root (j : Option (Fin 3)) : (q.map G.embed).IsRoot (withExtra v e j) := by
    rw [← layout_map_eq E F]
    cases j with
    | none => exact eroot
    | some j =>
      change ((q.map E.embed).map F.embed).eval (F.embed (r j)) = 0
      rw [Polynomial.eval_map_apply, show (q.map E.embed).eval (r j) = 0 from rr j, map_zero]
  have eq := factor_eq_of_indexed_roots (withExtra v e) Finset.univ
    (withExtra_injective ord.injective nz) (fun j _ => root j)
    (by simpa only [natDegree_map_eq_of_injective G.embed.injective, Finset.card_univ,
        Fintype.card_option, Fintype.card_fin] using qd)
  rw [indexedHull_withExtra] at eq
  exact ⟨G, v, e, ⟨ord, U, edge, eq⟩⟩

theorem inner_left_exact_layout {q Z : K[X]} {c : Fin 5 → K} (M : Moments q Z c)
    (a : c 2 < 0) (u : MarkInterior c 1) (z : MarkInterior c 4) :
    c 4 < c 1 ∧ ∃ E : OrderedExtension K, ∃ (r : Fin 3 → E.carrier) (e : E.carrier),
      ExteriorRootLayout (q.map E.embed) r e (E.embed (c 2)) 0 := by
  refine ⟨inner_left_outers_overlap M a u z, ?_⟩
  obtain ⟨E, r, e, layout⟩ := three_unit_and_external_gap M.qDegree (Or.inl le_rfl)
    (paid_unit_three_of_mark_exterior M (by decide : (2 : Fin 5) ≠ 0) (Or.inl a))
    (left_inner_exterior_alternation M a u.1)
  exact ⟨E, r, e, by simpa only [map_zero] using layout⟩

theorem inner_right_exact_layout {q Z : K[X]} {c : Fin 5 → K} (M : Moments q Z c)
    (h : 1 < c 3) (u : MarkInterior c 1) (z : MarkInterior c 4) :
    c 4 < c 1 ∧ ∃ E : OrderedExtension K, ∃ (r : Fin 3 → E.carrier) (e : E.carrier),
      ExteriorRootLayout (q.map E.embed) r e 1 (E.embed (c 3)) := by
  refine ⟨inner_right_outers_overlap M h u z, ?_⟩
  obtain ⟨E, r, e, layout⟩ := three_unit_and_external_gap M.qDegree (Or.inr le_rfl)
    (paid_unit_three_of_mark_exterior M (by decide : (3 : Fin 5) ≠ 0) (Or.inr h))
    (right_inner_exterior_alternation M h z.2)
  exact ⟨E, r, e, by simpa only [map_one] using layout⟩

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
