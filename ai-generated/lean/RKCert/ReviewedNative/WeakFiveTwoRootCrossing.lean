module

public import RKCert.ReviewedNative.WeakFiveTwoRootLocalOrder

import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Exact crossed order from the two true inner windows

The comparison is at the polynomial integrand level. The ratio heuristic
is replaced by its factored numerator, and no rational function is integrated.
The nonnegative quadratic may vanish at an isolated interior point or endpoint.
-/

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

open Polynomial RKCert.ReviewedNative.WeakFive16 RKCert.ReviewedNative.PositiveRule19
open RKCert.ReviewedNative.FiniteOrderedSigns
open scoped Polynomial

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem exact_grid_nonneg {P : K[X]} {l r : K} (lr : l < r) (pd : P.natDegree ≤ 19)
    (p : ∀ x ∈ Set.Ioo l r, 0 ≤ P.eval x) : 0 ≤ integral l r P := by
  rw [interval_exact _ _ _ pd]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (intervalWeight_pos lr i).le (p _ (intervalPoint_mem lr i))

private theorem exact_grid_nonpos {P : K[X]} {l r : K} (lr : l < r) (pd : P.natDegree ≤ 19)
    (p : ∀ x ∈ Set.Ioo l r, P.eval x ≤ 0) : integral l r P ≤ 0 := by
  rw [interval_exact _ _ _ pd]
  exact Finset.sum_nonpos fun i _ =>
    mul_nonpos_of_nonneg_of_nonpos (intervalWeight_pos lr i).le (p _ (intervalPoint_mem lr i))

private theorem exact_grid_pos_nonzero {P : K[X]} {l r : K} (lr : l < r) (pn : P ≠ 0)
    (pd : P.natDegree < 19) (p : ∀ x ∈ Set.Ioo l r, 0 ≤ P.eval x) : 0 < integral l r P := by
  obtain ⟨i,ni⟩ := exists_nonzero_grid_sample lr pn pd
  exact integral_pos_of_grid_samples lr pd.le (fun i => p _ (intervalPoint_mem lr i))
    ⟨i,lt_of_le_of_ne (p _ (intervalPoint_mem lr i)) ni.symm⟩

theorem crossed_inner_order_of_two_root_factor {p B Z : K[X]} {c : Fin 5 → K} {r s σ : K}
    (M : Moments (p*C σ) Z c) (F : SignedTwoRootFactor p B r s σ)
    (H : TwoRootWindow c r s) : c 3 < c 2 := by
  let u := c 1
  let a := c 2
  let h := c 3
  let z := c 4
  let Q := p*C σ
  let U : K[X] := X*(C u-X)
  let V : K[X] := (1-X)*(X-C z)
  have z0 : 0 < z := H.z0
  have rZ : z < r := H.zr
  have rA : r < a := H.ra
  have rH : r < h := H.rh
  have aS : a < s := H.as'
  have hS : h < s := H.hs'
  have sU : s < u := H.su
  have u1 : u < 1 := H.u1
  have up : 0 < U.eval r := by
    simp only [U,eval_mul,eval_sub,eval_X,eval_C]
    exact mul_pos (z0.trans rZ) (sub_pos.mpr (F.order.trans sU))
  have vp : 0 < V.eval r := by
    simp only [V,eval_mul,eval_sub,eval_X,eval_C,eval_one]
    exact mul_pos (sub_pos.mpr (F.order.trans (sU.trans u1))) (sub_pos.mpr rZ)
  have ud : U.natDegree ≤ 2 := by
    have hR : (C u - X : K[X]).natDegree ≤ 1 := by
      rw [← neg_sub, natDegree_neg, natDegree_X_sub_C]
    exact natDegree_mul_le_of_le natDegree_X.le hR
  have vd : V.natDegree ≤ 2 := natDegree_mul_le_of_le
    (unit_right_weight_degree (K := K)).le (natDegree_X_sub_C _).le
  have UQd : (U*Q).natDegree ≤ 6 := natDegree_mul_le_of_le ud M.qDegree
  have VQd : (V*Q).natDegree ≤ 6 := natDegree_mul_le_of_le vd M.qDegree
  have pref : 0 < integral 0 z (U*Q) := by
    have Un : U ≠ 0 := fun bad => by simp [bad] at up
    apply exact_grid_pos_nonzero z0 (mul_ne_zero Un M.qNonzero) (UQd.trans_lt (by decide))
    intro x hx
    have xru : x < r := hx.2.trans rZ
    have xsu : x < s := xru.trans F.order
    have q0 := mul_nonneg (F.nonneg x ⟨hx.1.le,(xsu.trans (sU.trans u1)).le⟩)
      (mul_nonneg_of_nonpos_of_nonpos (sub_neg.mpr xru).le (sub_neg.mpr xsu).le)
    rw [eval_mul,F.eval_oriented]
    simp only [U,eval_mul,eval_sub,eval_X,eval_C]
    exact mul_nonneg (mul_nonneg hx.1.le (sub_pos.mpr (xsu.trans sU)).le) q0
  have paidA : integral 0 a (U*Q) = 0 := by
    rw [show U*Q = -(X*(X-C u)*Q) by dsimp only [U]; ring,map_neg,M.forwardInner,neg_zero]
  have paidH : integral z h (V*Q) = 0 := by
    rw [show V*Q = -((1-X)*(C z-X)*Q) by dsimp only [V]; ring,map_neg,
      exact_integral_reverse _ h z,reverse_genuine_difference M,neg_zero,neg_zero]
  have negU : integral z a (U*Q) < 0 := by
    have sum := exact_integral_join (U*Q) 0 z a
    linarith only [pref,paidA,sum]
  let D := (C (U.eval r)*V - C (V.eval r)*U)*Q
  have dd : D.natDegree ≤ 6 := natDegree_mul_le_of_le
    (natDegree_sub_le_of_le ((natDegree_C_mul_le _ _).trans vd) ((natDegree_C_mul_le _ _).trans ud))
    M.qDegree
  have compare : integral z a D ≤ 0 := by
    apply exact_grid_nonpos (rZ.trans rA) (dd.trans (by decide))
    intro x hx
    let k := z*(1-x)*(u-r)+(r-z)*x*(1-u)
    have kp : 0 < k := add_pos
      (mul_pos (mul_pos z0 (sub_pos.mpr (hx.2.trans (aS.trans (sU.trans u1)))))
        (sub_pos.mpr (F.order.trans sU)))
      (mul_pos (mul_pos (sub_pos.mpr rZ) (z0.trans hx.1)) (sub_pos.mpr u1))
    have eqo : D.eval x = (B.eval x*(x-r)^2)*(k*(x-s)) := by
      calc D.eval x = (U.eval r*V.eval x-V.eval r*U.eval x)*Q.eval x := by
             simp only [D,eval_mul,eval_sub,eval_C]
           _ = _ := by
             rw [show Q.eval x = B.eval x*((x-r)*(x-s)) from F.eval_oriented x]
             simp only [U,V,eval_mul,eval_sub,eval_X,eval_C,eval_one,k]
             ring
    rw [eqo]
    exact mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (F.nonneg x ⟨(z0.trans hx.1).le,(hx.2.trans (aS.trans (sU.trans u1))).le⟩)
        (sq_nonneg _)) (mul_neg_of_pos_of_neg kp (sub_neg.mpr (hx.2.trans aS))).le
  have algebra : integral z a D =
      U.eval r*integral z a (V*Q) - V.eval r*integral z a (U*Q) := by
    have hU : integral z a (C (V.eval r) * U * Q) =
        V.eval r * integral z a (U * Q) := by rw [mul_assoc, integral_C_mul]
    have hV : integral z a (C (U.eval r) * V * Q) =
        U.eval r * integral z a (V * Q) := by rw [mul_assoc, integral_C_mul]
    dsimp only [D]
    rw [sub_mul, map_sub, hV, hU]
  have negV : integral z a (V*Q) < 0 := by
    have inner := mul_neg_of_pos_of_neg vp negU
    have hh : U.eval r*integral z a (V*Q)<0 := by linarith only [compare,algebra,inner]
    exact neg_of_mul_neg_right hh up.le
  by_contra! bad
  have ah : a ≤ h := bad
  have non : integral a h (V*Q) ≤ 0 := by
    rcases ah.lt_or_eq with lt | same
    · apply exact_grid_nonpos lt (VQd.trans (by decide))
      intro x hx
      have xr : r < x := rA.trans hx.1
      have xs : x < s := hx.2.trans hS
      have q0 := mul_nonpos_of_nonneg_of_nonpos
        (F.nonneg x ⟨(z0.trans (rZ.trans xr)).le,(xs.trans (sU.trans u1)).le⟩)
        (mul_neg_of_pos_of_neg (sub_pos.mpr xr) (sub_neg.mpr xs)).le
      rw [eval_mul,F.eval_oriented]
      simp only [V,eval_mul,eval_sub,eval_X,eval_C,eval_one]
      exact mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg (sub_pos.mpr (xs.trans (sU.trans u1))).le (sub_pos.mpr (rZ.trans xr)).le) q0
    · rw [same]
      simp only [integral_apply,sub_self,le_refl]
  have joined := exact_integral_join (V*Q) z a h
  linarith only [negV, non, joined, paidH]

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
