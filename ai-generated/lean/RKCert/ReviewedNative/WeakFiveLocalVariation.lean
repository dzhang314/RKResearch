module

public import RKCert.ReviewedNative.ERKOrder16WeakFiveMoments
public import RKCert.ReviewedNative.OneWeightOrderedSigns
public import RKCert.ReviewedNative.OrderedAlternationDegree

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

open Polynomial RKCert.ReviewedNative.WeakFive16 RKCert.ReviewedNative.PositiveRule19
open RKCert.ReviewedNative.FiniteOrderedSigns
open scoped Polynomial

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem integral_C_mul (l r c : K) (P : K[X]) :
    integral l r (C c * P) = c * integral l r P := by
  simpa only [Polynomial.smul_eq_C_mul, smul_eq_mul] using (integral l r).map_smul c P

theorem unit_right_weight_degree : (1-X : K[X]).natDegree = 1 := by
  have alg : (1-X : K[X]) = -(X-C (1:K)) := by simp [neg_sub]
  rw [alg, natDegree_neg, natDegree_X_sub_C]

theorem exact_integral_reverse (P : K[X]) (a b : K) : integral b a P = -integral a b P := by
  simp only [integral_apply]
  ring

theorem exact_integral_join (P : K[X]) (a b c : K) :
    integral a b P + integral b c P = integral a c P := by
  simp only [integral_apply]
  ring

theorem variation_of_affine_tests {q W : K[X]} {l r : K}
    (lr : l < r) (qn : q ≠ 0) (qd : q.natDegree ≤ 4) (wd : W.natDegree ≤ 1)
    (pos : ∀ x ∈ Set.Ioo l r, 0 < W.eval x)
    (m₀ : integral l r (W*q) = 0) (m₁ : integral l r (W*q*X) = 0) :
    HasAlternationsOn q (Set.Ioo l r) 2 := by
  apply HasAlternationsOn.of_grid lr
  apply grid_variation_of_positive_moments lr qn (qd.trans_lt (by decide)) (by omega) pos
  intro j
  fin_cases j
  · simpa only [Fin.val_zero, pow_zero, mul_one] using m₀
  · simpa using m₁

theorem forward_pair_inside {q Z : K[X]} {c : Fin 5 → K} (M : Moments q Z c) (u0 : 0 < c 1) :
    HasAlternationsOn q (Set.Ioo 0 (c 1)) 2 := by
  refine variation_of_affine_tests u0 M.qNonzero M.qDegree natDegree_X.le ?_ M.forwardFirst ?_
  · intro x hx
    simpa only [eval_X] using hx.1
  · rw [show X*q*X = X^2*q by ring]
    exact M.forwardSecond

theorem reverse_pair_inside {q Z : K[X]} {c : Fin 5 → K} (M : Moments q Z c) (z1 : c 4 < 1) :
    HasAlternationsOn q (Set.Ioo (c 4) 1) 2 := by
  refine variation_of_affine_tests z1 M.qNonzero M.qDegree (unit_right_weight_degree (K := K)).le
    ?_ M.reverseFirst ?_
  · intro x hx
    simpa only [eval_sub, eval_one, eval_X] using sub_pos.mpr hx.2
  · rw [show (1-X)*q*X = (1-X)*q-(1-X)^2*q by ring, map_sub,
      M.reverseFirst, M.reverseSecond, sub_zero]

theorem forward_pair_negative_clock {q Z : K[X]} {c : Fin 5 → K}
    (M : Moments q Z c) (u0 : c 1 < 0) : HasAlternationsOn q (Set.Ioo (c 1) 0) 2 := by
  refine variation_of_affine_tests u0 M.qNonzero M.qDegree (by simp)
    (W := (-X : K[X])) ?_ ?_ ?_
  · intro x hx
    simpa only [eval_neg, eval_X] using neg_pos.mpr hx.2
  · rw [neg_mul, map_neg, exact_integral_reverse (X*q) 0 (c 1), M.forwardFirst, neg_zero, neg_zero]
  · rw [show (-X)*q*X = -(X^2*q) by ring, map_neg, exact_integral_reverse (X^2*q) 0 (c 1),
      M.forwardSecond, neg_zero, neg_zero]

theorem reverse_pair_clock_above_one {q Z : K[X]} {c : Fin 5 → K}
    (M : Moments q Z c) (z1 : 1 < c 4) : HasAlternationsOn q (Set.Ioo 1 (c 4)) 2 := by
  have a₀ : integral (c 4) 1 ((1-X)*q) = 0 := M.reverseFirst
  have a₁ : integral (c 4) 1 ((1-X)*q*X) = 0 := by
    rw [show (1-X)*q*X = (1-X)*q-(1-X)^2*q by ring, map_sub, a₀, M.reverseSecond, sub_zero]
  refine variation_of_affine_tests z1 M.qNonzero M.qDegree (W := -(1-X : K[X])) ?_ ?_ ?_ ?_
  · rw [natDegree_neg, unit_right_weight_degree]
  · intro x hx
    simpa only [eval_neg, eval_sub, eval_one, eval_X] using neg_pos.mpr (sub_neg.mpr hx.1)
  · rw [neg_mul, map_neg, exact_integral_reverse ((1-X)*q) (c 4) 1, a₀, neg_zero, neg_zero]
  · rw [neg_mul, neg_mul, map_neg, exact_integral_reverse ((1-X)*q*X) (c 4) 1, a₁, neg_zero, neg_zero]

theorem forward_outer_hull_zero {q Z : K[X]} {c : Fin 5 → K} (M : Moments q Z c) :
    integral 0 (c 1) (X*(X-C (c 1))*q) = 0 := by
  rw [show X*(X-C (c 1))*q = X^2*q-C (c 1)*(X*q) by ring, map_sub, integral_C_mul,
     M.forwardFirst, M.forwardSecond, mul_zero, sub_zero]

theorem reverse_outer_hull_zero {q Z : K[X]} {c : Fin 5 → K} (M : Moments q Z c) :
    integral (c 4) 1 ((1-X)*(C (c 4)-X)*q) = 0 := by
  rw [show (1-X)*(C (c 4)-X)*q = (1-X)^2*q-C (1-c 4)*((1-X)*q) by
    simp only [map_sub, map_one]; ring, map_sub, integral_C_mul,
     M.reverseFirst, M.reverseSecond, mul_zero, sub_zero]

theorem forward_genuine_difference {q Z : K[X]} {c : Fin 5 → K} (M : Moments q Z c) :
    integral (c 1) (c 2) (X*(X-C (c 1))*q) = 0 := by
  have w := exact_integral_join (X*(X-C (c 1))*q) 0 (c 1) (c 2)
  rw [forward_outer_hull_zero M, M.forwardInner, zero_add] at w
  exact w

theorem reverse_genuine_difference {q Z : K[X]} {c : Fin 5 → K} (M : Moments q Z c) :
    integral (c 3) (c 4) ((1-X)*(C (c 4)-X)*q) = 0 := by
  have w := exact_integral_join ((1-X)*(C (c 4)-X)*q) (c 3) (c 4) 1
  rw [reverse_outer_hull_zero M, M.reverseInner, add_zero] at w
  exact w

theorem moments_scale_nonzero {q Z : K[X]} {c : Fin 5 → K} (M : Moments q Z c) {t : K}
    (tn : t ≠ 0) : Moments (q*C t) Z c := by
  have sc {l r : K} {R : K[X]} (paid : integral l r (R*q) = 0) :
      integral l r (R*(q*C t))=0 := by
    rw [show R*(q*C t)=C t*(R*q) by ring, integral_C_mul, paid, mul_zero]
  refine ⟨mul_ne_zero M.qNonzero (C_ne_zero.mpr tn), (natDegree_mul_C tn).trans_le M.qDegree,
    M.origin, M.clockSimple, ?_, M.middleFactor, sc M.forwardFirst, sc M.forwardSecond,
    sc M.forwardInner, sc M.reverseFirst, sc M.reverseSecond, sc M.reverseInner, ?_⟩
  · intro j
    refine ⟨(M.active j).1, ?_⟩
    rw [eval_mul, eval_C]
    exact mul_ne_zero (M.active j).2 tn
  · intro H hd
    rw [show X*(1-X)*((q*C t)*nodalTail c Z)*H = C t*(X*(1-X)*(q*nodalTail c Z)*H) by ring,
      integral_C_mul, M.weightedMoments H hd, mul_zero]

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
