module

public import RKCert.ReviewedNative.ERKOrder16WeakFiveDoubleExterior
public import RKCert.ReviewedNative.ERKOrder16WeakFiveExteriorCharge
public import RKCert.ReviewedNative.ERKOrder16WeakFiveCrossedInnerSquare
public import RKCert.ReviewedNative.DisjointTwoMomentWindows
import RKCert.ReviewedNative.LegendreEnergyRatio
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace RKCert.ReviewedNative.WeakFive16

open Polynomial RKCert.ReviewedNative.PositiveRule19
open RKCert.ReviewedNative.FiniteOrderedSigns RKCert.ReviewedNative.LegendreEnergy
open RKCert.ReviewedNative.EvenExteriorBarycentric
open scoped BigOperators Classical

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem Moments.scale_profile {q Z : K[X]} {c : Fin 5 → K}
    (M : Moments q Z c) {t : K} (tn : t ≠ 0) :
    Moments (q * C t) Z c := by
  have sc {l r : K} {R : K[X]} (eq : integral l r (R * q) = 0) :
      integral l r (R * (q * C t)) = 0 := by
    rw [show R * (q * C t) = C t * (R * q) by ring, integral_C_mul, eq, mul_zero]
  refine {
    qNonzero := mul_ne_zero M.qNonzero (C_ne_zero.mpr tn)
    qDegree := (natDegree_mul_C tn).trans_le M.qDegree
    origin := M.origin
    clockSimple := M.clockSimple
    active := ?_
    middleFactor := M.middleFactor
    forwardFirst := sc M.forwardFirst
    forwardSecond := sc M.forwardSecond
    forwardInner := sc M.forwardInner
    reverseFirst := sc M.reverseFirst
    reverseSecond := sc M.reverseSecond
    reverseInner := sc M.reverseInner
    weightedMoments := ?_ }
  · intro i
    refine ⟨(M.active i).1, ?_⟩
    rw [eval_mul, eval_C]
    exact mul_ne_zero (M.active i).2 tn
  · intro R rd
    have eq : (X * (1 - X)) * ((q * C t) * nodalTail c Z) * R =
        C t * ((X * (1 - X)) * (q * nodalTail c Z) * R) := by ring
    rw [eq, integral_C_mul, M.weightedMoments R rd, mul_zero]

private theorem exact_join (l m r : K) (P : K[X]) :
    integral l m P + integral m r P = integral l r P := by
  simp only [integral_apply]
  ring

private theorem reverse_zero {l r : K} {P : K[X]} (h : integral l r P = 0) :
    integral r l P = 0 := by
  simp only [integral_apply] at h ⊢
  linarith only [h]

private theorem exact_pos {l r : K} {P : K[X]} (lr : l < r)
    (degree : P.natDegree ≤ 19) (pos : ∀ x ∈ Set.Ioo l r, 0 < P.eval x) :
    0 < integral l r P :=
  integral_pos_of_grid_samples lr degree (fun i => (pos _ (intervalPoint_mem lr i)).le)
    ⟨0, pos _ (intervalPoint_mem lr 0)⟩

private theorem exact_neg {l r : K} {P : K[X]} (lr : l < r)
    (degree : P.natDegree ≤ 19) (neg : ∀ x ∈ Set.Ioo l r, P.eval x < 0) :
    integral l r P < 0 := by
  have h := exact_pos (P := -P) lr (by simpa only [natDegree_neg] using degree)
    (fun x hx => by simpa only [eval_neg] using neg_pos.mpr (neg x hx))
  rw [map_neg] at h
  exact neg_pos.mp h

private theorem exact_nonneg {l r : K} {P : K[X]} (lr : l < r)
    (degree : P.natDegree ≤ 19) (pos : ∀ x ∈ Set.Ioo l r, 0 ≤ P.eval x) :
    0 ≤ integral l r P := by
  rw [interval_exact l r P degree]
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (intervalWeight_pos lr i).le (pos _ (intervalPoint_mem lr i))

private theorem sub_X_degree (r : K) : (C r - X : K[X]).natDegree ≤ 1 := by
  simpa only [natDegree_C, natDegree_X, max_eq_right (Nat.zero_le 1)] using
    (natDegree_sub_le (C r) (X : K[X]))

private theorem Moments.no_crossed_inner_exteriors {q Z : K[X]} {c : Fin 5 → K}
    (M : Moments q Z c) (u0 : 0 < c 1) (u1 : c 1 < 1) (z0 : 0 < c 4) (z1 : c 4 < 1)
    (h0 : c 3 < 0) (a1 : 1 < c 2) (atZero : 0 < q.eval 0)
    (outsideRight : ∀ x : K, 1 ≤ x → 0 < q.eval x)
    (actual : integral (c 1) (c 2) (X * (X - C (c 1)) * q) = 0) : False := by
  let u := c 1
  let a := c 2
  let z := c 4
  let F : K[X] := X * (X - C u) * q
  have uz : u < z := M.outer_order_of_negative_reverse_inner u0 u1 z0 h0
  obtain ⟨gap, mean⟩ := gap_nonneg_and_right_mean_pos M.qDegree u0 uz z1 atZero
    (outsideRight 1 le_rfl) M.forwardFirst M.forwardSecond M.reverseFirst M.reverseSecond
  have fd : F.natDegree ≤ 6 :=
    natDegree_mul_le_of_le (natDegree_mul_le_of_le natDegree_X.le (natDegree_X_sub_C u).le) M.qDegree
  have pay : F.natDegree ≤ 19 := fd.trans (by decide : 6 ≤ 19)
  have ev (x : K) : F.eval x = x * (x - u) * q.eval x := by
    simp only [F, eval_mul, eval_sub, eval_X, eval_C]
  have mid : 0 < integral z 1 F := by
    have eq : F = C (1 - u) * q - C (2 - u) * ((1 - X) * q) + (1 - X)^2 * q := by
      simp only [F, map_sub, map_one, map_ofNat]
      ring
    change 0 < (integral (c 4) 1) F
    rw [eq, map_add, map_sub, integral_C_mul, integral_C_mul,
      M.reverseFirst, M.reverseSecond, mul_zero, sub_zero, add_zero]
    exact mul_pos (sub_pos.mpr u1) mean
  have leftPart : 0 ≤ integral u z F := exact_nonneg uz pay (by
    intro x hx
    rw [ev]
    exact mul_nonneg (mul_nonneg (u0.trans hx.1).le (sub_nonneg.mpr hx.1.le))
      (gap x ⟨hx.1.le, hx.2.le⟩))
  have rightPart : 0 < integral 1 a F := exact_pos a1 pay (by
    intro x hx
    rw [ev]
    exact mul_pos (mul_pos (zero_lt_one.trans hx.1) (sub_pos.mpr (u1.trans hx.1)))
      (outsideRight x hx.1.le))
  have h1 := exact_join u z 1 F
  have h2 := exact_join u 1 a F
  have eq : integral u a F = 0 := actual
  linarith only [h1, h2, eq, leftPart, mid, rightPart]

private theorem exterior_count_formula {c : Fin 5 → K}
    (u0 : 0 < c 1) (a0 : 0 < c 2) (h1 : c 3 < 1) (z1 : c 4 < 1) :
    (exteriorMarkedClocks c).card =
      (if 1 < c 1 then 1 else 0) + (if 1 < c 2 then 1 else 0) +
      (if c 3 < 0 then 1 else 0) + (if c 4 < 0 then 1 else 0) := by
  classical
  let S : Finset (Fin 5) := Finset.univ.erase 0
  let e (i : Fin 5) : Prop := c i < 0 ∨ 1 < c i
  have sEq : S = {1, 2, 3, 4} := by
    change (Finset.univ : Finset (Fin 5)).erase 0 = {1, 2, 3, 4}
    decide
  have n1 : (1 : Fin 5) ∉ ({2, 3, 4} : Finset (Fin 5)) := by decide
  have n2 : (2 : Fin 5) ∉ ({3, 4} : Finset (Fin 5)) := by decide
  have n3 : (3 : Fin 5) ∉ ({4} : Finset (Fin 5)) := by decide
  have h : (exteriorMarkedClocks c).card = ∑ i ∈ S, if e i then (1 : ℕ) else 0 :=
    (Finset.sum_boole (R := ℕ) e S).symm
  rw [sEq, Finset.sum_insert n1, Finset.sum_insert n2, Finset.sum_insert n3,
    Finset.sum_singleton] at h
  rw [h]
  simp only [e, not_lt_of_ge u0.le, not_lt_of_ge a0.le, not_lt_of_ge h1.le,
    not_lt_of_ge z1.le, false_or, or_false]
  omega

/-- In the actual quartic packet, any two exterior marks have one of
the three published opposed-side shapes. No marked endpoint signs or
numerical order of the two interior clocks is assumed. -/
theorem Moments.doubleExteriorShapes_of_count_eq_two {q Z : K[X]} {c : Fin 5 → K}
    (M : Moments q Z c) (qd : q.natDegree = 4) (two : (exteriorMarkedClocks c).card = 2) :
    DoubleExteriorShapes c := by
  classical
  let t : K := q.leadingCoeff⁻¹
  let Q := q * C t
  have tn : t ≠ 0 := inv_ne_zero (leadingCoeff_ne_zero.mpr M.qNonzero)
  have qm : Q.Monic := monic_mul_leadingCoeff_inv M.qNonzero
  have deg : Q.natDegree = 4 := (natDegree_mul_C tn).trans qd
  have N : Moments Q Z c := M.scale_profile tn
  have alt : HasAlternationsOn Q (Set.Ioo (0 : K) 1) 4 := by
    simpa only [two] using N.unit_alternations_of_exterior_count
  obtain ⟨ql, qr, _, _⟩ := exterior_of_even_alternations (n := 2) (by decide)
    qm (by simpa using deg) (by simpa using alt)
  let u := c 1
  let a := c 2
  let h := c 3
  let z := c 4
  let F : K[X] := X * (X - C u) * Q
  let G : K[X] := (1 - X) * (C z - X) * Q
  have fd : F.natDegree ≤ 19 :=
    (natDegree_mul_le_of_le (natDegree_mul_le_of_le natDegree_X.le (natDegree_X_sub_C u).le)
      N.qDegree : F.natDegree ≤ 6).trans (by decide : 6 ≤ 19)
  have oneSub : (1 - X : K[X]).natDegree ≤ 1 := by
    simpa only [map_one] using sub_X_degree (1 : K)
  have gd : G.natDegree ≤ 19 :=
    (natDegree_mul_le_of_le (natDegree_mul_le_of_le oneSub (sub_X_degree z))
      N.qDegree : G.natDegree ≤ 6).trans (by decide : 6 ≤ 19)
  have ld : (X * Q).natDegree ≤ 19 :=
    (natDegree_mul_le_of_le natDegree_X.le N.qDegree : (X * Q).natDegree ≤ 5).trans
      (by decide : 5 ≤ 19)
  have rd : ((1 - X) * Q).natDegree ≤ 19 :=
    (natDegree_mul_le_of_le oneSub N.qDegree : ((1 - X) * Q).natDegree ≤ 5).trans
      (by decide : 5 ≤ 19)
  have Fval (x : K) : F.eval x = x * (x - u) * Q.eval x := by
    simp only [F, eval_mul, eval_sub, eval_X, eval_C]
  have Gval (x : K) : G.eval x = (1 - x) * (z - x) * Q.eval x := by
    simp only [G, eval_mul, eval_sub, eval_X, eval_C, eval_one]
  have fu : integral 0 u F = 0 := by
    have l1 : integral 0 u (X * Q) = 0 := N.forwardFirst
    have l2 : integral 0 u (X^2 * Q) = 0 := N.forwardSecond
    have eq : F = X^2 * Q - C u * (X * Q) := by dsimp only [F]; ring
    rw [eq, map_sub, integral_C_mul, l1, l2, mul_zero, sub_zero]
  have fa : integral 0 a F = 0 := N.forwardInner
  have gz : integral z 1 G = 0 := by
    have r1 : integral z 1 ((1 - X) * Q) = 0 := N.reverseFirst
    have r2 : integral z 1 ((1 - X)^2 * Q) = 0 := N.reverseSecond
    have eq : G = (1 - X)^2 * Q - C (1 - z) * ((1 - X) * Q) := by
      simp only [G, map_sub, map_one]
      ring
    rw [eq, map_sub, integral_C_mul, r1, r2, mul_zero, sub_zero]
  have gh : integral h 1 G = 0 := N.reverseInner
  have fDiff : integral u a F = 0 := by
    have j := exact_join 0 u a F
    linarith only [j, fu, fa]
  have gDiff : integral h z G = 0 := by
    have j := exact_join h z 1 G
    linarith only [j, gz, gh]
  have u0 : 0 < u := by
    apply lt_of_not_ge
    intro bad
    have nz : u ≠ 0 := N.clock_ne_zero (i := 1) (by decide)
    have un := lt_of_le_of_ne bad nz
    have e := exact_neg (P := X * Q) un ld (by
      intro x hx
      rw [eval_mul, eval_X]
      exact mul_neg_of_neg_of_pos hx.2 (ql x hx.2.le))
    have l1 : integral 0 u (X * Q) = 0 := N.forwardFirst
    exact e.ne (reverse_zero l1)
  have z1 : z < 1 := by
    apply lt_of_not_ge
    intro bad
    have nz : z ≠ 1 := (N.active 4).1
    have zp := lt_of_le_of_ne bad nz.symm
    have e := exact_neg (P := (1 - X) * Q) zp rd (by
      intro x hx
      simp only [eval_mul, eval_sub, eval_one, eval_X]
      exact mul_neg_of_neg_of_pos (sub_neg.mpr hx.1) (qr x hx.1.le))
    have r1 : integral z 1 ((1 - X) * Q) = 0 := N.reverseFirst
    exact e.ne (reverse_zero r1)
  have a0 : 0 < a := by
    apply lt_of_not_ge
    intro bad
    have na : a ≠ 0 := N.clock_ne_zero (i := 2) (by decide)
    have an := lt_of_le_of_ne bad na
    have e := exact_pos an fd (by
      intro x hx
      rw [Fval]
      exact mul_pos (mul_pos_of_neg_of_neg hx.2 (sub_neg.mpr (hx.2.trans u0))) (ql x hx.2.le))
    exact e.ne' (reverse_zero fa)
  have h1 : h < 1 := by
    apply lt_of_not_ge
    intro bad
    have nh : h ≠ 1 := (N.active 3).1
    have hp := lt_of_le_of_ne bad nh.symm
    have e := exact_pos hp gd (by
      intro x hx
      rw [Gval]
      exact mul_pos (mul_pos_of_neg_of_neg (sub_neg.mpr hx.1) (sub_neg.mpr (z1.trans hx.1)))
        (qr x hx.1.le))
    exact e.ne' (reverse_zero gh)
  have noRight (ur : 1 < u) (ar : 1 < a) : False := by
    have ua : u ≠ a := fun eq => (by decide : (1 : Fin 5) ≠ 2) (N.clockSimple eq)
    rcases lt_or_gt_of_ne ua with ua | au
    · have e := exact_pos ua fd (by
        intro x hx
        rw [Fval]
        have x1 := ur.trans hx.1
        exact mul_pos (mul_pos (zero_lt_one.trans x1) (sub_pos.mpr hx.1)) (qr x x1.le))
      exact e.ne' fDiff
    · have e := exact_neg au fd (by
        intro x hx
        rw [Fval]
        have x1 := ar.trans hx.1
        exact mul_neg_of_neg_of_pos
          (mul_neg_of_pos_of_neg (zero_lt_one.trans x1) (sub_neg.mpr hx.2)) (qr x x1.le))
      exact e.ne (reverse_zero fDiff)
  have noLeft (zl : z < 0) (hl : h < 0) : False := by
    have hz : h ≠ z := fun eq => (by decide : (3 : Fin 5) ≠ 4) (N.clockSimple eq)
    rcases lt_or_gt_of_ne hz with hz | zh
    · have e := exact_pos hz gd (by
        intro x hx
        rw [Gval]
        have x0 := hx.2.trans zl
        exact mul_pos (mul_pos (sub_pos.mpr (x0.trans zero_lt_one)) (sub_pos.mpr hx.2))
          (ql x x0.le))
      exact e.ne' gDiff
    · have e := exact_neg zh gd (by
        intro x hx
        rw [Gval]
        have x0 := hx.2.trans hl
        exact mul_neg_of_neg_of_pos
          (mul_neg_of_pos_of_neg (sub_pos.mpr (x0.trans zero_lt_one)) (sub_neg.mpr hx.1))
          (ql x x0.le))
      exact e.ne (reverse_zero gDiff)
  have counted :
      (if 1 < u then (1 : ℕ) else 0) + (if 1 < a then 1 else 0) +
        (if h < 0 then 1 else 0) + (if z < 0 then 1 else 0) = 2 :=
    (exterior_count_formula u0 a0 h1 z1).symm.trans two
  have originFreeH : h ≠ 0 := N.clock_ne_zero (i := 3) (by decide)
  have originFreeZ : z ≠ 0 := N.clock_ne_zero (i := 4) (by decide)
  by_cases ur : 1 < u
  · have na : ¬ 1 < a := fun ar => noRight ur ar
    have ai : a < 1 := lt_of_le_of_ne (le_of_not_gt na) (N.active 2).1
    by_cases zl : z < 0
    · have hi : 0 < h := lt_of_le_of_ne (le_of_not_gt (noLeft zl)) originFreeH.symm
      exact Or.inl ⟨zl, ur, a0, ai, hi, h1⟩
    · have hl : h < 0 := by
        by_contra nh
        norm_num [ur, na, zl, nh] at counted
      have zi : 0 < z := lt_of_le_of_ne (le_of_not_gt zl) originFreeZ.symm
      exact Or.inr (Or.inr ⟨hl, ur, zi, z1, a0, ai⟩)
  · have ui : u < 1 := lt_of_le_of_ne (le_of_not_gt ur) (N.active 1).1
    by_cases ar : 1 < a
    · by_cases zl : z < 0
      · have hi : 0 < h := lt_of_le_of_ne (le_of_not_gt (noLeft zl)) originFreeH.symm
        exact Or.inr (Or.inl ⟨zl, ar, u0, ui, hi, h1⟩)
      · have hl : h < 0 := by
          by_contra nh
          norm_num [ur, ar, zl, nh] at counted
        have zi : 0 < z := lt_of_le_of_ne (le_of_not_gt zl) originFreeZ.symm
        exact (N.no_crossed_inner_exteriors u0 ui zi z1 hl ar (ql 0 le_rfl) qr fDiff).elim
    · by_cases zl : z < 0
      · have nh : ¬ h < 0 := noLeft zl
        norm_num [ur, ar, zl, nh] at counted
      · by_cases hl : h < 0 <;> norm_num [ur, ar, zl, hl] at counted

/-- Actual paid packets cannot have two exterior marks. The degree
four needed by the published consumer is earned from the variation charge. -/
theorem Moments.no_two_exterior_marks {q Z : K[X]} {c : Fin 5 → K}
    (M : Moments q Z c) : (exteriorMarkedClocks c).card ≠ 2 := by
  intro two
  have charge := M.exterior_count_add_two_le_degree
  have upper := M.qDegree
  have qd : q.natDegree = 4 := by omega
  exact M.no_classified_double_exterior qd (M.doubleExteriorShapes_of_count_eq_two qd two)

theorem Moments.exterior_count_le_one {q Z : K[X]} {c : Fin 5 → K}
    (M : Moments q Z c) : (exteriorMarkedClocks c).card ≤ 1 := by
  have charge := M.exterior_count_add_two_le_degree
  have upper := M.qDegree
  have no := M.no_two_exterior_marks
  omega

end
end RKCert.ReviewedNative.WeakFive16

namespace RKResearch.Certified.ERK16

open Polynomial Module RKCert.ReviewedNative.WeakFive16 RKCert.Endpoint.WeightedClock
open RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse.Thin

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The ordinary native five-site packet has at most one exterior
marked clock; all moments and labels still come from the same tableau. -/
theorem width24_weak_five_exterior_count_le_one
    {A : Matrix (Fin 24) (Fin 24) K} {b w : Fin 24 → K} {Q P : K[X]}
    {U : Submodule K (Fin 24 → K)}
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : RKResearch.HasOrder 16 A b)
    (seven : finrank K (zeroSpace A 7) = 7)
    (L : Width24OrdinaryWeakHead A b U w Q P)
    (five : 5 ≤ (weightedSites (reflectedClock A) (reverseContrast A b Q P)).card) :
    ∃ (q Z : K[X]) (c : Fin 5 → K), Moments q Z c ∧ (exteriorMarkedClocks c).card ≤ 1 := by
  obtain ⟨q, Z, c, M⟩ := width24_weak_five_moments_of_ordinary_head ha ho seven L five
  exact ⟨q, Z, c, M, M.exterior_count_le_one⟩

end
end RKResearch.Certified.ERK16
