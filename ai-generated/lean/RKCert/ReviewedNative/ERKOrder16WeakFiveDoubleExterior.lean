module

public import RKCert.ReviewedNative.ERKOrder16WeakFiveAdapter
public import RKCert.ReviewedNative.SaturatedEvenUnweightedMoment
public import RKCert.ReviewedNative.SquareFactorOrderedSigns
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # The actual three possible double-exterior directions

Only the six existing global tests and displayed local ports are consumed.
No splitting, quartic norm, or one-exterior claim enters. -/
namespace RKCert.ReviewedNative.WeakFive16

open Polynomial RKCert.Endpoint RKCert.ReviewedNative.PositiveRule19
open RKCert.ReviewedNative.FiniteOrderedSigns
open RKCert.ReviewedNative.SaturatedEvenMoment
open RKCert.ReviewedNative.EvenExteriorBarycentric

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def innerPair (b c : K) : K[X] := (X-C b)*(X-C c)

private theorem innerPair_monic (b c : K) : (innerPair b c).Monic :=
  (monic_X_sub_C b).mul (monic_X_sub_C c)

private theorem innerPair_degree (b c : K) : (innerPair b c).natDegree = 2 := by
  simp only [innerPair, natDegree_mul (X_sub_C_ne_zero b) (X_sub_C_ne_zero c),
    natDegree_X_sub_C] <;> decide

private theorem one_sub_X_degree : (1-X : K[X]).natDegree ≤ 1 := by
  have e : (1-X : K[X]) = -(X-C (1 : K)) := by simp [neg_sub]
  rw [e, natDegree_neg, natDegree_X_sub_C]

private theorem sub_X_degree (r : K) : (C r-X : K[X]).natDegree ≤ 1 := by
  simpa only [natDegree_C, natDegree_X, max_eq_right (Nat.zero_le 1)] using
    (natDegree_sub_le (C r) (X : K[X]))

private theorem integral_scale (l r d : K) (P : K[X]) :
    integral l r (C d*P) = d*integral l r P := by
  simpa only [smul_eq_C_mul, smul_eq_mul] using (integral l r).map_smul d P

private theorem integral_join (a b c : K) (P : K[X]) :
    integral a b P+integral b c P=integral a c P := by
  simp only [integral_apply]
  ring

private theorem pos_integral_of_pos_on {P : K[X]} {a b : K}
    (ab : a < b) (degree : P.natDegree ≤ 19)
    (p : ∀ x ∈ Set.Ioo a b, 0 < P.eval x) :
    0 < integral a b P := by
  refine integral_pos_of_grid_samples ab degree
    (fun i => (p _ (intervalPoint_mem ab i)).le) ?_
  exact ⟨0, p _ (intervalPoint_mem ab 0)⟩

/-- With two exterior and two interior nodal factors, absorbing the
two squared interior factors into the sampled polynomial gives four
unit changes of the actual quartic. Every exterior value is positive
by the same finite Lagrange lemma. -/
private theorem quartic_pos_outside_of_six {q : K[X]} {l r b c : K}
    (qm : q.Monic) (qd : q.natDegree = 4) (l0 : l < 0) (r1 : 1 < r)
    (mesh : ∀ R : K[X], R.natDegree ≤ 5 →
      integral 0 1 (fourWeight l 0 1 r*(q*innerPair b c)*R)=0) :
    (∀ x : K, x ≤ 0 → 0 < q.eval x) ∧ (∀ x : K, 1 ≤ x → 0 < q.eval x) := by
  let H := innerPair b c
  let W := fourWeight l 0 1 r
  let P := q*H^2
  have hd : H.natDegree ≤ 2 := (innerPair_degree b c).le
  have hn : H ≠ 0 := (innerPair_monic b c).ne_zero
  have hd2 : (H^2).natDegree ≤ 4 := by
    have le := natDegree_pow_le (p := H) (n := 2)
    omega
  have pd : P.natDegree ≤ 8 := natDegree_mul_le_of_le qd.le hd2
  have pn : P ≠ 0 := mul_ne_zero qm.ne_zero (pow_ne_zero _ hn)
  have wDegree : W.natDegree ≤ 4 := by
    dsimp only [W, fourWeight]
    exact natDegree_mul_le_of_le
      (natDegree_mul_le_of_le
        (natDegree_mul_le_of_le (natDegree_X_sub_C l).le (natDegree_X_sub_C (0 : K)).le)
        (sub_X_degree 1)) (sub_X_degree r)
  have wpos (x : K) (hx : x ∈ Set.Ioo (0 : K) 1) : 0 < W.eval x := by
    simp only [W, fourWeight, eval_mul, eval_sub, eval_C, eval_X, sub_zero]
    exact mul_pos (mul_pos (mul_pos (sub_pos.mpr (l0.trans hx.1)) hx.1)
      (sub_pos.mpr hx.2)) (sub_pos.mpr (hx.2.trans r1))
  have paid (i : Fin 4) : integral 0 1 (W*P*X^i.val)=0 := by
    let R := H*X^i.val
    have rd : R.natDegree ≤ 5 := by
      have bound : R.natDegree ≤ 2+i.val :=
        natDegree_mul_le_of_le hd (natDegree_X_pow_le _)
      have hi := i.isLt
      omega
    have fit : W*P*X^i.val = W*(q*H)*R := by dsimp only [P, R]; ring
    rw [fit]
    exact mesh R rd
  have pq : (q*H^2).natDegree ≤ 8 := pd
  have cuts : HasAlternationsOn (q*H^2) (Set.Ioo (0 : K) 1) 4 :=
    HasAlternationsOn.of_grid zero_lt_one
      (grid_variation_of_positive_moments (U := W) (m := 4) zero_lt_one pn
        (by omega) (by omega) wpos paid)
  have qCuts : HasAlternationsOn q (Set.Ioo (0 : K) 1) 4 := cuts.of_mul_sq
  obtain ⟨lo, hi, _, _⟩ := exterior_of_even_alternations (n := 2) (by decide)
    qm (by simpa using qd) (by simpa using qCuts)
  exact ⟨lo, hi⟩

/-- The common bilateral contradiction for the two interior factors.
Only two true zeros, at the actual exterior outer ends of their
integration windows, are needed in addition to the six global tests. -/
theorem two_exterior_gluing_impossible {q : K[X]} {l r b c : K}
    (qm : q.Monic) (qd : q.natDegree = 4) (l0 : l < 0) (r1 : 1 < r)
    (b0 : 0 < b) (b1 : b < 1) (c0 : 0 < c) (c1 : c < 1)
    (mesh : ∀ R : K[X], R.natDegree ≤ 5 →
      integral 0 1 (fourWeight l 0 1 r*(q*innerPair b c)*R)=0)
    (leftZero : integral 0 r (X*(X-C b)*q)=0)
    (rightZero : integral l 1 ((1-X)*(X-C b)*q)=0) : False := by
  let T := q*innerPair b c
  have tm : T.Monic := qm.mul (innerPair_monic b c)
  have td : T.natDegree = 6 := by
    simp only [T, natDegree_mul qm.ne_zero (innerPair_monic b c).ne_zero,
      qd, innerPair_degree] <;> decide
  have Tpos : 0 < integral 0 1 T := integral_pos_of_six tm td l0 r1 mesh
  obtain ⟨ql, qr⟩ := quartic_pos_outside_of_six qm qd l0 r1 mesh
  let L := C (1-c)*(X*(X-C b)*q)
  let R := C (-c)*((1-X)*(X-C b)*q)
  have Ll : integral 0 r L = 0 := by
    dsimp only [L]
    rw [integral_scale, leftZero, mul_zero]
  have Rr : integral l 1 R = 0 := by
    dsimp only [R]
    rw [integral_scale, rightZero, mul_zero]
  have Ld : L.natDegree ≤ 6 :=
    (natDegree_C_mul_le _ _).trans
      (natDegree_mul_le_of_le (natDegree_mul_le_of_le natDegree_X.le
        (natDegree_X_sub_C b).le) qd.le)
  have Rd : R.natDegree ≤ 6 :=
    (natDegree_C_mul_le _ _).trans
      (natDegree_mul_le_of_le (natDegree_mul_le_of_le one_sub_X_degree
        (natDegree_X_sub_C b).le) qd.le)
  have posL : 0 < integral 1 r L := by
    apply pos_integral_of_pos_on r1 (Ld.trans (by decide))
    intro x hx
    simp only [L, eval_mul, eval_sub, eval_X, eval_C]
    exact mul_pos (sub_pos.mpr c1)
      (mul_pos (mul_pos (zero_lt_one.trans hx.1) (sub_pos.mpr (b1.trans hx.1))) (qr x hx.1.le))
  have posR : 0 < integral l 0 R := by
    apply pos_integral_of_pos_on l0 (Rd.trans (by decide))
    intro x hx
    simp only [R, eval_mul, eval_sub, eval_X, eval_C, eval_one]
    exact mul_pos_of_neg_of_neg (neg_lt_zero.mpr c0)
      (mul_neg_of_neg_of_pos
        (mul_neg_of_pos_of_neg (sub_pos.mpr (hx.2.trans zero_lt_one))
          (sub_neg.mpr (hx.2.trans b0))) (ql x hx.2.le))
  have eq : L+R = T := by
    simp only [L, R, T, innerPair, map_sub, map_neg, map_one]
    ring
  have one := integral_join 0 1 r L
  have two := integral_join l 0 1 R
  rw [Ll] at one
  rw [Rr] at two
  rw [← eq, map_add] at Tpos
  linarith only [one, two, Tpos, posL, posR]

private theorem Moments.left_linear {q Z : K[X]} {c : Fin 5 → K}
    (H : Moments q Z c) (b : K) : integral 0 (c 1) (X*(X-C b)*q)=0 := by
  rw [show X*(X-C b)*q = X^2*q-C b*(X*q) by ring,
    map_sub, integral_scale, H.forwardSecond, H.forwardFirst, mul_zero, sub_zero]

private theorem Moments.right_linear {q Z : K[X]} {c : Fin 5 → K}
    (H : Moments q Z c) (b : K) : integral (c 4) 1 ((1-X)*(X-C b)*q)=0 := by
  rw [show (1-X)*(X-C b)*q = C (1-b)*((1-X)*q)-(1-X)^2*q by
      simp only [map_sub, map_one]; ring,
    map_sub, integral_scale, H.reverseFirst, H.reverseSecond, mul_zero, sub_zero]

/-- Normalize the same actual profile. Preserve the original global
hull through the supplied exact negative exterior factorization. -/
private theorem Moments.no_gluing_of_exterior_factor {q Z : K[X]} {c : Fin 5 → K}
    (H : Moments q Z c) (qd : q.natDegree = 4) {l r b h : K}
    (l0 : l < 0) (r1 : 1 < r) (b0 : 0 < b) (b1 : b < 1) (h0 : 0 < h) (h1 : h < 1)
    (factor : fourWeight l 0 1 r*innerPair b h = -(X*(1-X)*nodalTail c Z))
    (left : integral 0 r (X*(X-C b)*q)=0)
    (right : integral l 1 ((1-X)*(X-C b)*q)=0) : False := by
  let t : K := q.leadingCoeff⁻¹
  let Q := q*C t
  have tn : t ≠ 0 := inv_ne_zero (leadingCoeff_ne_zero.mpr H.qNonzero)
  have qm : Q.Monic := monic_mul_leadingCoeff_inv H.qNonzero
  have deg : Q.natDegree = 4 := (natDegree_mul_C tn).trans qd
  have loc (x y : K) (S : K[X]) (paid : integral x y (S*q)=0) :
      integral x y (S*Q)=0 := by
    rw [show S*Q = C t*(S*q) by dsimp only [Q]; ring,
      integral_scale, paid, mul_zero]
  have mesh (R : K[X]) (rd : R.natDegree ≤ 5) :
      integral 0 1 (fourWeight l 0 1 r*(Q*innerPair b h)*R)=0 := by
    have eq : fourWeight l 0 1 r*(Q*innerPair b h)*R =
        C (-t)*(X*(1-X)*(q*nodalTail c Z)*R) := by
      calc
        _ = (fourWeight l 0 1 r*innerPair b h)*(q*C t)*R := by dsimp only [Q]; ring
        _ = _ := by rw [factor, map_neg]; ring
    rw [eq, integral_scale, H.weightedMoments R rd, mul_zero]
  exact two_exterior_gluing_impossible qm deg l0 r1 b0 b1 h0 h1 mesh
    (loc _ _ _ left) (loc _ _ _ right)

theorem Moments.no_opposed_outer_double_exterior {q Z : K[X]} {c : Fin 5 → K}
    (H : Moments q Z c) (qd : q.natDegree = 4)
    (z0 : c 4 < 0) (u1 : 1 < c 1)
    (a0 : 0 < c 2) (a1 : c 2 < 1) (h0 : 0 < c 3) (h1 : c 3 < 1) : False := by
  apply H.no_gluing_of_exterior_factor qd z0 u1 a0 a1 h0 h1
  · simp only [fourWeight, innerPair, nodalTail, H.middleFactor, map_zero, map_one, sub_zero]
    ring
  · exact H.left_linear (c 2)
  · exact H.right_linear (c 2)

theorem Moments.no_left_crossed_double_exterior {q Z : K[X]} {c : Fin 5 → K}
    (H : Moments q Z c) (qd : q.natDegree = 4)
    (z0 : c 4 < 0) (a1 : 1 < c 2)
    (u0 : 0 < c 1) (u1 : c 1 < 1) (h0 : 0 < c 3) (h1 : c 3 < 1) : False := by
  apply H.no_gluing_of_exterior_factor qd z0 a1 u0 u1 h0 h1
  · simp only [fourWeight, innerPair, nodalTail, H.middleFactor, map_zero, map_one, sub_zero]
    ring
  · exact H.forwardInner
  · exact H.right_linear (c 1)

theorem Moments.no_right_crossed_double_exterior {q Z : K[X]} {c : Fin 5 → K}
    (H : Moments q Z c) (qd : q.natDegree = 4)
    (h0 : c 3 < 0) (u1 : 1 < c 1)
    (z0 : 0 < c 4) (z1 : c 4 < 1) (a0 : 0 < c 2) (a1 : c 2 < 1) : False := by
  apply H.no_gluing_of_exterior_factor qd h0 u1 z0 z1 a0 a1
  · simp only [fourWeight, innerPair, nodalTail, H.middleFactor, map_zero, map_one, sub_zero]
    ring
  · exact H.left_linear (c 4)
  · rw [show (1-X)*(X-C (c 4))*q = -((1-X)*(C (c 4)-X)*q) by ring,
      map_neg, H.reverseInner, neg_zero]

/-- The three shapes selected by the independent actual exterior-location
classification. This does not itself infer that classification. -/
def DoubleExteriorShapes (c : Fin 5 → K) : Prop :=
  (c 4 < 0 ∧ 1 < c 1 ∧ 0 < c 2 ∧ c 2 < 1 ∧ 0 < c 3 ∧ c 3 < 1) ∨
  (c 4 < 0 ∧ 1 < c 2 ∧ 0 < c 1 ∧ c 1 < 1 ∧ 0 < c 3 ∧ c 3 < 1) ∨
  (c 3 < 0 ∧ 1 < c 1 ∧ 0 < c 4 ∧ c 4 < 1 ∧ 0 < c 2 ∧ c 2 < 1)

theorem Moments.no_classified_double_exterior {q Z : K[X]} {c : Fin 5 → K}
    (H : Moments q Z c) (qd : q.natDegree = 4) : ¬ DoubleExteriorShapes c := by
  unfold DoubleExteriorShapes
  rintro (⟨z0, u1, a0, a1, h0, h1⟩ | ⟨z0, a1, u0, u1, h0, h1⟩ |
    ⟨h0, u1, z0, z1, a0, a1⟩)
  · exact H.no_opposed_outer_double_exterior qd z0 u1 a0 a1 h0 h1
  · exact H.no_left_crossed_double_exterior qd z0 a1 u0 u1 h0 h1
  · exact H.no_right_crossed_double_exterior qd h0 u1 z0 z1 a0 a1

end
end RKCert.ReviewedNative.WeakFive16

namespace RKResearch.Certified.ERK16

open RKResearch Polynomial Module
open RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse
open RKResearch.Certified.Graded.Reverse.Thin
open RKCert.Endpoint RKCert.Endpoint.WeightedClock
open RKCert.ReviewedNative.WeakFive16

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem width24_weak_five_excludes_classified_double_exterior
    {A : Matrix (Fin 24) (Fin 24) K} {b : Fin 24 → K} {Q P : K[X]}
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 16 A b)
    (seven : finrank K (zeroSpace A 7) = 7)
    {U : Submodule K (Fin 24 → K)} {w : Fin 24 → K}
    (L : Width24OrdinaryWeakHead A b U w Q P)
    (five : 5 ≤ (weightedSites (reflectedClock A) (reverseContrast A b Q P)).card) :
    ∃ (q Z : K[X]) (c : Fin 5 → K), Moments q Z c ∧
      (q.natDegree = 4 → ¬ DoubleExteriorShapes c) := by
  obtain ⟨q, Z, c, H⟩ := width24_weak_five_moments_of_ordinary_head ha ho seven L five
  exact ⟨q, Z, c, H, H.no_classified_double_exterior⟩

end
end RKResearch.Certified.ERK16
