module

public import RKCert.ReviewedNative.ERKOrder16WeakFiveCubicWindows
public import RKCert.ReviewedNative.CubicAnchoredCutoff
public import RKCert.ReviewedNative.CubicJacobiPencilSix

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

@[expose] public section

/-! # The cubic weak-five packet is impossible -/

namespace RKCert.ReviewedNative.WeakFive16

open Polynomial RKCert.Endpoint
open RKCert.ReviewedNative.PositiveRule19 RKCert.ReviewedNative.FiniteOrderedSigns
open RKCert.ReviewedNative.CubicEnd RKCert.ReviewedNative.AnchorMean
open RKCert.ReviewedNative.JacobiSix

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem strict_integral_on_open {l r : K} {P : K[X]}
    (lr : l < r) (degree : P.natDegree ≤ 19)
    (positive : ∀ x ∈ Set.Ioo l r, 0 < P.eval x) : 0 < integral l r P :=
  integral_pos_of_grid_samples lr degree
    (fun i => (positive _ (intervalPoint_mem lr i)).le)
    ⟨0, positive _ (intervalPoint_mem lr 0)⟩

/-- The true right inner port cannot vanish above a cutoff on which q is
positive. Endpoints are oriented; no upper bound on h is presumed. -/
private theorem right_inner_below_positive_tail {q : K[X]} {B z h : K}
    (B1 : B < 1) (zB : z < B) (h1 : h ≠ 1) (degree : q.natDegree ≤ 17)
    (qpos : ∀ x : K, B ≤ x → 0 < q.eval x)
    (test : integral h 1 ((1-X)*(C z-X)*q) = 0) :
    h < B := by
  let G : K[X] := (1-X)*(C z-X)*q
  have gd : G.natDegree ≤ 19 := by
    have left : (1-X : K[X]).natDegree ≤ 1 := by
      simpa only [natDegree_one, natDegree_X, max_eq_right (Nat.zero_le 1)] using
        (natDegree_sub_le (1 : K[X]) (X : K[X]))
    have right : (C z-X : K[X]).natDegree ≤ 1 := by
      simpa only [natDegree_C, natDegree_X, max_eq_right (Nat.zero_le 1)] using
        (natDegree_sub_le (C z) (X : K[X]))
    exact natDegree_mul_le_of_le (natDegree_mul_le_of_le left right) degree
  have zero : integral h 1 G = 0 := test
  by_contra! high
  rcases lt_trichotomy h (1 : K) with below | equal | above
  · have nd : (-G).natDegree ≤ 19 := by simpa only [natDegree_neg] using gd
    have pos : 0 < integral h 1 (-G) := by
      apply strict_integral_on_open below nd
      intro x hx
      have bx : B ≤ x := high.trans hx.1.le
      have zx : z < x := zB.trans_le bx
      have ev : G.eval x < 0 := by
        simp only [G, eval_mul, eval_sub, eval_one, eval_X, eval_C]
        exact mul_neg_of_neg_of_pos
          (mul_neg_of_pos_of_neg (sub_pos.mpr hx.2) (sub_neg.mpr zx)) (qpos x bx)
      simpa only [eval_neg] using neg_pos.mpr ev
    rw [map_neg, zero, neg_zero] at pos
    exact (lt_irrefl (0 : K)) pos
  · exact h1 equal
  · have pos : 0 < integral 1 h G := by
      apply strict_integral_on_open above gd
      intro x hx
      have bx : B < x := B1.trans hx.1
      have zx : z < x := zB.trans bx
      simp only [G, eval_mul, eval_sub, eval_one, eval_X, eval_C]
      exact mul_pos (mul_pos_of_neg_of_neg (sub_neg.mpr hx.1) (sub_neg.mpr zx))
        (qpos x bx.le)
    have backwards : integral 1 h G = 0 := by
      rw [integral_apply] at zero ⊢
      exact sub_eq_zero.mpr (sub_eq_zero.mp zero).symm
    exact (ne_of_gt pos) backwards

private theorem cubicHull_monic (u a h z : K) : (cubicHull u a h z).Monic :=
  (monic_X_sub_C u).mul ((monic_X_sub_C z).mul ((monic_X_sub_C a).mul (monic_X_sub_C h)))

private theorem cubicHull_degree (u a h z : K) : (cubicHull u a h z).natDegree = 4 := by
  have ah := (monic_X_sub_C a).mul (monic_X_sub_C h)
  have zah := (monic_X_sub_C z).mul ah
  rw [cubicHull, natDegree_mul (monic_X_sub_C u).ne_zero zah.ne_zero,
    natDegree_mul (monic_X_sub_C z).ne_zero ah.ne_zero,
    natDegree_mul (monic_X_sub_C a).ne_zero (monic_X_sub_C h).ne_zero]
  norm_num [natDegree_X_sub_C]

/-- The exact degree-seven product with all six checked moments. -/
theorem CubicWindow.product_profile {q : K[X]} {u a h z : K}
    (W : CubicWindow q u a h z) :
    (q*cubicHull u a h z).Monic ∧ (q*cubicHull u a h z).natDegree = 7 ∧
      OrthogonalSix (q*cubicHull u a h z) := by
  have nm := cubicHull_monic u a h z
  have nd : (q*cubicHull u a h z).natDegree = 7 := by
    rw [natDegree_mul W.monic.ne_zero nm.ne_zero, W.degree, cubicHull_degree]
  exact ⟨W.monic.mul nm, nd, W.globalZero⟩

/-- The scalar coefficient is earned for the literal product, not assumed. -/
theorem CubicWindow.product_in_jacobi_pencil {q : K[X]} {u a h z : K}
    (W : CubicWindow q u a h z) :
    ∃ alpha : K, q*cubicHull u a h z = J7 K+C alpha*J6 K := by
  obtain ⟨nm, nd, moments⟩ := W.product_profile
  exact monic_seven_pencil nm nd moments

/-- Both actual anchors certify positivity of the whole product at and
above the cutoff; no scalar positivity or knot-order premise is added. -/
theorem OrientedCubicWindow.product_positive_above_cut {q : K[X]} {u a h z : K}
    (O : OrientedCubicWindow q u a h z) :
    ∀ x : K, (14 : K)/15 ≤ x → 0 < (q*cubicHull u a h z).eval x := by
  have W := O.window
  have R := W.reflected
  obtain ⟨us, _, cutoff⟩ := positive_of_monic_cubic_end_moments W.monic W.degree
    O.leftPositive O.rightPositive W.uOff.2 O.overlap O.orientation
    (by simpa only [integral_zero_left] using W.leftFirst)
    (by simpa only [integral_zero_left] using W.leftSecond)
    (by simpa only [integral_zero_left, cubicStar, reflectCubic] using R.leftFirst)
    (by simpa only [integral_zero_left, cubicStar, reflectCubic] using R.leftSecond)
  let B : K := 14/15
  have uB : u < B := us.trans (by dsimp [B]; norm_num)
  have zu : z < u := by linarith only [O.overlap]
  have zB := zu.trans uB
  have fzero : (formalPrimitive (anchorPair u*q)).eval a = 0 := by
    simpa only [integral_zero_left, anchorPair] using W.leftInner
  have aB : a < B := by
    by_contra! high
    exact (ne_of_gt (cutoff a high).2) fzero
  have hB : h < B :=
    right_inner_below_positive_tail (by dsimp [B]; norm_num) zB W.hOff.2
      (W.degree.le.trans (by decide)) (fun x hx => (cutoff x hx).1) W.rightInner
  intro x hx
  change B ≤ x at hx
  simp only [cubicHull, eval_mul, eval_sub, eval_X, eval_C]
  exact mul_pos (cutoff x hx).1
    (mul_pos (sub_pos.mpr (uB.trans_le hx))
      (mul_pos (sub_pos.mpr (zB.trans_le hx))
        (mul_pos (sub_pos.mpr (aB.trans_le hx)) (sub_pos.mpr (hB.trans_le hx)))))

theorem OrientedCubicWindow.impossible {q : K[X]} {u a h z : K}
    (O : OrientedCubicWindow q u a h z) : False := by
  obtain ⟨nm, nd, moments⟩ := O.window.product_profile
  exact not_monic_seven_positive_at_cut_points nm nd moments
    (O.product_positive_above_cut _ le_rfl) (O.product_positive_above_cut _ (by norm_num))

/-- The original weak-five twelve-moment packet cannot have a cubic
profile. The original q is normalized and oriented inside the proof. -/
theorem Moments.natDegree_ne_three {q Z : K[X]} {c : Fin 5 → K}
    (M : Moments q Z c) : q.natDegree ≠ 3 := by
  intro deg
  rcases M.oriented_cubic_window deg with original | reflected
  · exact original.impossible
  · exact reflected.impossible

end
end RKCert.ReviewedNative.WeakFive16
