module

public import RKCert.ReviewedNative.ERKOrder16WeakFiveMoments
public import RKCert.ReviewedNative.SquareFactorOrderedSigns

import RKCert.ReviewedNative.OneWeightOrderedSigns
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace RKCert.ReviewedNative.WeakFive16

open Polynomial RKCert.Endpoint
open RKCert.ReviewedNative.PositiveRule19 RKCert.ReviewedNative.FiniteOrderedSigns

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Actual non-origin hull using the four original chronological labels. -/
def cubicHull (u a h z : K) : K[X] :=
  (X-C u)*((X-C z)*((X-C a)*(X-C h)))

/-- Only this literal reflection is allowed in the scalar window argument. -/
def cubicStar (q : K[X]) : K[X] := -(q.comp (1-X))

/-- The exact scalar tests retained from the actual twelve-moment record.
The origin nonvanishing hypothesis is not needed after normalization. -/
structure CubicWindow (q : K[X]) (u a h z : K) : Prop where
  monic : q.Monic
  degree : q.natDegree = 3
  uOff : u ≠ 0 ∧ u ≠ 1
  aOff : a ≠ 0 ∧ a ≠ 1
  hOff : h ≠ 0 ∧ h ≠ 1
  zOff : z ≠ 0 ∧ z ≠ 1
  leftFirst : integral 0 u (X*q) = 0
  leftSecond : integral 0 u (X^2*q) = 0
  leftInner : integral 0 a (X*(X-C u)*q) = 0
  rightFirst : integral z 1 ((1-X)*q) = 0
  rightSecond : integral z 1 ((1-X)^2*q) = 0
  rightInner : integral h 1 ((1-X)*(C z-X)*q) = 0
  globalZero : ∀ R : K[X], R.natDegree ≤ 5 →
    integral 0 1 (X*(1-X)*(q*cubicHull u a h z)*R) = 0

theorem Moments.cubic_window {q Z : K[X]} {c : Fin 5 → K}
    (M : Moments q Z c) (deg : q.natDegree = 3) :
    CubicWindow (q*C q.leadingCoeff⁻¹) (c 1) (c 2) (c 3) (c 4) := by
  let t : K := q.leadingCoeff⁻¹
  let Q := q*C t
  have tne : t ≠ 0 := inv_ne_zero (leadingCoeff_ne_zero.mpr M.qNonzero)
  have mq : Q.Monic := monic_mul_leadingCoeff_inv M.qNonzero
  have dq : Q.natDegree = 3 := (natDegree_mul_C tne).trans deg
  have off (i : Fin 5) (hi : i ≠ 0) : c i ≠ 0 ∧ c i ≠ 1 :=
    ⟨M.clock_ne_zero hi, (M.active i).1⟩
  have scale (l r : K) (P R : K[X]) (m : integral l r (P*q*R) = 0) :
      integral l r (P*Q*R) = 0 := by
    have eq : P*Q*R = t • (P*q*R) := by
      dsimp [Q]
      rw [smul_eq_C_mul]
      ring
    rw [eq, map_smul, m, smul_zero]
  have loc (l r : K) (P : K[X]) (m : integral l r (P*q) = 0) :
      integral l r (P*Q) = 0 := by
    simpa only [mul_one] using scale l r P 1 (by simpa only [mul_one] using m)
  refine ⟨mq, dq, off 1 (by decide), off 2 (by decide), off 3 (by decide), off 4 (by decide),
    loc 0 _ X M.forwardFirst, loc 0 _ (X^2) M.forwardSecond,
    loc 0 _ (X*(X-C (c 1))) M.forwardInner,
    loc _ 1 (1-X) M.reverseFirst, loc _ 1 ((1-X)^2) M.reverseSecond,
    loc _ 1 ((1-X)*(C (c 4)-X)) M.reverseInner, ?_⟩
  intro R hd
  have hull : cubicHull (c 1) (c 2) (c 3) (c 4) = nodalTail c Z := by
    rw [cubicHull, nodalTail, M.middleFactor, mul_assoc]
  have m : integral 0 1
      (X*(1-X)*q*(cubicHull (c 1) (c 2) (c 3) (c 4)*R)) = 0 := by
    simpa only [hull, mul_assoc] using M.weightedMoments R hd
  let H := cubicHull (c 1) (c 2) (c 3) (c 4)
  have h := scale 0 1 (X*(1-X)) (H*R) m
  rw [← mul_assoc (X*(1-X)*Q) H R, mul_assoc (X*(1-X)) Q H] at h
  exact h

private theorem one_sub_X_degree : (1-X : K[X]).natDegree = 1 := by
  have e : (1-X : K[X]) = -(X-C (1 : K)) := by simp [neg_sub]
  rw [e, natDegree_neg, natDegree_X_sub_C]

private theorem one_sub_X_leading : (1-X : K[X]).leadingCoeff = -1 := by
  have e : (1-X : K[X]) = -(X-C (1 : K)) := by simp [neg_sub]
  rw [e, leadingCoeff_neg, leadingCoeff_X_sub_C]

private theorem comp_twice (P : K[X]) : (P.comp (1-X)).comp (1-X) = P := by
  rw [comp_assoc]
  have e : (1-X : K[X]).comp (1-X) = X := by
    simp only [sub_comp, one_comp, X_comp, sub_sub_cancel]
  rw [e, comp_X]

private theorem off_reflected {x : K} (h : x ≠ 0 ∧ x ≠ 1) :
    1-x ≠ 0 ∧ 1-x ≠ 1 := by
  refine ⟨sub_ne_zero.mpr h.2.symm, ?_⟩
  intro hc
  exact h.1 (by linarith only [hc])

private theorem reflected_left_zero {P : K[X]} {x : K} (h : integral x 1 P = 0) :
    integral 0 (1-x) (-(P.comp (1-X))) = 0 := by
  rw [map_neg, integral_reflect, h, neg_zero]

private theorem reflected_right_zero {P : K[X]} {x : K} (h : integral 0 x P = 0) :
    integral (1-x) 1 (-(P.comp (1-X))) = 0 := by
  have e := integral_reflect (P.comp (1-X)) (1-x)
  rw [sub_sub_cancel, comp_twice, h] at e
  rw [map_neg, ← e, neg_zero]

private theorem hull_comp (u a h z : K) :
    (cubicHull u a h z).comp (1-X) = cubicHull (1-z) (1-h) (1-a) (1-u) := by
  simp only [cubicHull, mul_comp, sub_comp, X_comp, C_comp, C_sub, C_1]
  ring

/-- Explicitly swap the two outer lengths and the two actual inner marks.
Every local/global equality is transported with its exact sign. -/
theorem CubicWindow.reflected {q : K[X]} {u a h z : K} (W : CubicWindow q u a h z) :
    CubicWindow (cubicStar q) (1-z) (1-h) (1-a) (1-u) := by
  have monic : (cubicStar q).Monic := by
    change (cubicStar q).leadingCoeff = 1
    have degree : (1-X : K[X]).natDegree ≠ 0 := by rw [one_sub_X_degree]; decide
    rw [cubicStar, leadingCoeff_neg, leadingCoeff_comp degree, W.monic.leadingCoeff,
      one_sub_X_leading, W.degree] <;> norm_num
  have deg : (cubicStar q).natDegree = 3 := by
    simpa only [cubicStar, natDegree_neg, natDegree_comp, one_sub_X_degree, mul_one] using W.degree
  refine ⟨monic, deg, off_reflected W.zOff, off_reflected W.hOff,
    off_reflected W.aOff, off_reflected W.uOff, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have e : X*cubicStar q = -(((1-X)*q).comp (1-X)) := by
      simp only [cubicStar, mul_comp, sub_comp, one_comp, X_comp, sub_sub_cancel, mul_neg]
    rw [e]
    exact reflected_left_zero W.rightFirst
  · have e : X^2*cubicStar q = -(((1-X)^2*q).comp (1-X)) := by
      simp only [cubicStar, mul_comp, pow_comp, sub_comp, one_comp, X_comp,
        sub_sub_cancel, mul_neg]
    rw [e]
    exact reflected_left_zero W.rightSecond
  · have e : X*(X-C (1-z))*cubicStar q = -(((1-X)*(C z-X)*q).comp (1-X)) := by
      simp only [cubicStar, mul_comp, sub_comp, one_comp, X_comp, C_comp, C_sub, C_1]
      ring
    rw [e]
    exact reflected_left_zero W.rightInner
  · have e : (1-X)*cubicStar q = -((X*q).comp (1-X)) := by
      simp only [cubicStar, mul_comp, X_comp, mul_neg]
    rw [e]
    exact reflected_right_zero W.leftFirst
  · have e : (1-X)^2*cubicStar q = -((X^2*q).comp (1-X)) := by
      simp only [cubicStar, mul_comp, pow_comp, X_comp, mul_neg]
    rw [e]
    exact reflected_right_zero W.leftSecond
  · have e : (1-X)*(C (1-u)-X)*cubicStar q = -((X*(X-C u)*q).comp (1-X)) := by
      simp only [cubicStar, mul_comp, sub_comp, X_comp, C_comp, C_sub, C_1]
      ring
    rw [e]
    exact reflected_right_zero W.leftInner
  · intro R rd
    have small : (R.comp (1-X)).natDegree ≤ 5 := by
      simpa only [natDegree_comp, one_sub_X_degree, mul_one] using rd
    have paid := W.globalZero (R.comp (1-X)) small
    have e : X*(1-X)*(cubicStar q*cubicHull (1-z) (1-h) (1-a) (1-u))*R =
        -((X*(1-X)*(q*cubicHull u a h z)*(R.comp (1-X))).comp (1-X)) := by
      simp only [cubicStar, comp_twice, hull_comp, mul_comp, sub_comp, one_comp, X_comp]
      ring
    rw [e]
    simpa only [sub_zero] using reflected_left_zero (x := (0 : K)) paid

private theorem reverse_interval_zero {l r : K} {P : K[X]}
    (m : integral l r P = 0) : integral r l P = 0 := by
  rw [integral_apply] at m ⊢
  exact sub_eq_zero.mpr (sub_eq_zero.mp m).symm

private theorem two_changes {q U : K[X]} {l r : K} (lr : l < r)
    (qn : q ≠ 0) (qd : q.natDegree = 3) (ud : U.natDegree ≤ 1)
    (pos : ∀ x ∈ Set.Ioo l r, 0 < U.eval x)
    (m0 : integral l r (U*q) = 0) (m1 : integral l r (U*q*X) = 0) :
    HasAlternationsOn q (Set.Ioo l r) 2 := by
  refine HasAlternationsOn.of_grid lr
    (grid_variation_of_positive_moments (U := U) (m := 2) lr qn (by omega) (by omega) pos ?_)
  intro k
  fin_cases k
  · simpa using m0
  · simpa using m1

private theorem CubicWindow.negative_left_changes {q : K[X]} {u a h z : K}
    (W : CubicWindow q u a h z) (un : u < 0) :
    HasAlternationsOn q (Set.Ioo u 0) 2 := by
  have first : integral u 0 ((-X)*q) = 0 := by
    rw [neg_mul, map_neg, reverse_interval_zero W.leftFirst, neg_zero]
  have second : integral u 0 ((-X)*q*X) = 0 := by
    rw [show (-X)*q*X = -(X^2*q) by ring, map_neg,
      reverse_interval_zero W.leftSecond, neg_zero]
  have degree : (-X : K[X]).natDegree ≤ 1 := by
    simpa only [natDegree_neg] using (natDegree_X.le : (X : K[X]).natDegree ≤ 1)
  apply two_changes un W.monic.ne_zero W.degree degree _ first second
  intro x hx
  simpa only [eval_neg, eval_X] using neg_pos.mpr hx.2

private theorem CubicWindow.positive_left_changes {q : K[X]} {u a h z : K}
    (W : CubicWindow q u a h z) (up : 0 < u) :
    HasAlternationsOn q (Set.Ioo 0 u) 2 := by
  have second : integral 0 u (X*q*X) = 0 := by
    rw [show X*q*X = X^2*q by ring]
    exact W.leftSecond
  have degree : (X : K[X]).natDegree ≤ 1 := by simp
  apply two_changes up W.monic.ne_zero W.degree degree _ W.leftFirst second
  intro x hx
  simpa only [eval_X] using hx.1

private theorem CubicWindow.positive_right_changes {q : K[X]} {u a h z : K}
    (W : CubicWindow q u a h z) (zp : z < 1) :
    HasAlternationsOn q (Set.Ioo z 1) 2 := by
  have second : integral z 1 ((1-X)*q*X) = 0 := by
    rw [show (1-X)*q*X = (1-X)*q-(1-X)^2*q by ring,
      map_sub, W.rightFirst, W.rightSecond, sub_self]
  apply two_changes zp W.monic.ne_zero W.degree one_sub_X_degree.le _ W.rightFirst second
  intro x hx
  simpa only [eval_sub, eval_one, eval_X] using sub_pos.mpr hx.2

/-- The global negative-u witness uses the strictly positive weight
X(1-X)(X-u); the potentially vanishing nodal square stays in P. -/
private theorem CubicWindow.negative_left_global_changes {q : K[X]} {u a h z : K}
    (W : CubicWindow q u a h z) (un : u < 0) :
    HasAlternationsOn q (Set.Ioo (0 : K) 1) 3 := by
  let T := (X-C z)*((X-C a)*(X-C h))
  let U : K[X] := X*(1-X)*(X-C u)
  let P := q*T^2
  have tm : T.Monic := (monic_X_sub_C z).mul
    ((monic_X_sub_C a).mul (monic_X_sub_C h))
  have td : T.natDegree ≤ 3 :=
    natDegree_mul_le_of_le (natDegree_X_sub_C z).le
      (natDegree_mul_le_of_le (natDegree_X_sub_C a).le (natDegree_X_sub_C h).le)
  have t2 : (T^2).natDegree ≤ 6 := (natDegree_pow_le (p := T) (n := 2)).trans (by omega)
  have pd : P.natDegree ≤ 9 := natDegree_mul_le_of_le W.degree.le t2
  have pn : P ≠ 0 := mul_ne_zero W.monic.ne_zero (pow_ne_zero _ tm.ne_zero)
  have ud : U.natDegree ≤ 3 :=
    natDegree_mul_le_of_le (natDegree_mul_le_of_le natDegree_X.le one_sub_X_degree.le)
      (natDegree_X_sub_C u).le
  have pos : ∀ x ∈ Set.Ioo (0 : K) 1, 0 < U.eval x := by
    intro x hx
    simp only [U, eval_mul, eval_sub, eval_X, eval_one, eval_C]
    exact mul_pos (mul_pos hx.1 (sub_pos.mpr hx.2)) (sub_pos.mpr (un.trans hx.1))
  have paid (k : Fin 3) : integral 0 1 (U*P*X^k.val) = 0 := by
    let R := T*X^k.val
    have le : R.natDegree ≤ 3+k.val := natDegree_mul_le_of_le td (natDegree_X_pow_le _)
    have rd : R.natDegree ≤ 5 := by have ki := k.isLt; omega
    have hull : cubicHull u a h z = (X-C u)*T := rfl
    have fit : U*P*X^k.val = X*(1-X)*(q*cubicHull u a h z)*R := by
      dsimp only [U, P, R]
      rw [hull]
      ring
    rw [fit]
    exact W.globalZero R rd
  have lr : (0 : K) < 1 := zero_lt_one
  have three := grid_variation_of_positive_moments (m := 3) lr pn (by omega)
    (by omega) pos paid
  have alt : HasAlternationsOn (q*T^2) (Set.Ioo (0 : K) 1) 3 :=
    HasAlternationsOn.of_grid lr three
  exact alt.of_mul_sq

theorem CubicWindow.left_positive {q : K[X]} {u a h z : K}
    (W : CubicWindow q u a h z) : 0 < u := by
  by_contra! no
  have un := lt_of_le_of_ne no W.uOff.1
  have h2 := W.negative_left_changes un
  have h3 := W.negative_left_global_changes un
  have choice := (h2.add_open h3 un.le le_rfl (zero_lt_one : (0 : K) < 1).le).le_natDegree
  rw [W.degree] at choice
  omega

/-- Endpoint exclusion from the original tuple; signs and overlap are
paid by windows, not asserted by physical chronology. -/
theorem CubicWindow.paid_lengths {q : K[X]} {u a h z : K}
    (W : CubicWindow q u a h z) :
    0 < u ∧ 0 < 1-z ∧ u ≠ 1 ∧ 1 < u+(1-z) := by
  have up := W.left_positive
  have vp : 0 < 1-z := W.reflected.left_positive
  refine ⟨up, vp, W.uOff.2, ?_⟩
  by_contra! no
  have uz : u ≤ z := by linarith only [no]
  have zp : z < 1 := sub_pos.mp vp
  have hL := W.positive_left_changes up
  have hR := W.positive_right_changes zp
  have choice := (hL.add_open hR up.le uz zp.le).le_natDegree
  rw [W.degree] at choice
  omega

structure OrientedCubicWindow (q : K[X]) (u a h z : K) : Prop where
  window : CubicWindow q u a h z
  leftPositive : 0 < u
  rightPositive : 0 < 1-z
  overlap : 1 < u+(1-z)
  orientation : 0 ≤ u-(1-z)

theorem CubicWindow.orient {q : K[X]} {u a h z : K} (W : CubicWindow q u a h z) :
    OrientedCubicWindow q u a h z ∨
      OrientedCubicWindow (cubicStar q) (1-z) (1-h) (1-a) (1-u) := by
  by_cases ord : 0 ≤ u-(1-z)
  · obtain ⟨up, vp, _, over⟩ := W.paid_lengths
    exact Or.inl ⟨W, up, vp, over, ord⟩
  · have R := W.reflected
    obtain ⟨up, vp, _, over⟩ := R.paid_lengths
    have newOrder : 0 ≤ (1-z)-(1-(1-u)) := by linarith only [lt_of_not_ge ord]
    exact Or.inr ⟨R, up, vp, over, newOrder⟩

theorem Moments.oriented_cubic_window {q Z : K[X]} {c : Fin 5 → K}
    (M : Moments q Z c) (deg : q.natDegree = 3) :
    OrientedCubicWindow (q*C q.leadingCoeff⁻¹) (c 1) (c 2) (c 3) (c 4) ∨
      OrientedCubicWindow (cubicStar (q*C q.leadingCoeff⁻¹))
        (1-c 4) (1-c 3) (1-c 2) (1-c 1) :=
  (M.cubic_window deg).orient

end
end RKCert.ReviewedNative.WeakFive16
