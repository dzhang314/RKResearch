module

public import RKCert.ReviewedNative.WeakFivePrimitiveBalance
public import RKCert.ReviewedNative.WeakFiveInteriorRootModes
public import RKCert.ReviewedNative.ERKOrder16WeakFiveExteriorClassifier

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Push
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Exact location of a single external mark on the genuine packet

The two exterior directions of each surviving label are not conflated.
The wrong inner direction is ruled out by the square balance (overlap)
or the two disjoint pairs and genuine difference integral. The overlap
argument uses the seam-safe reflected balance, not a new q(1) assumption.
-/

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

open Polynomial RKCert.ReviewedNative.WeakFive16 RKCert.ReviewedNative.PositiveRule19
open RKCert.ReviewedNative.FiniteOrderedSigns RKCert.ReviewedNative.EvenExteriorBarycentric
open scoped Polynomial

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

abbrev MarkInterior (c : Fin 5 → K) (i : Fin 5) : Prop := c i ∈ Set.Ioo 0 1

inductive MarkSector (c : Fin 5 → K) : Prop
  | allInterior (inside : AllFourMarksInterior c)
  | outerLeft (z : c 4 < 0) (u : MarkInterior c 1) (a : MarkInterior c 2) (h : MarkInterior c 3)
  | outerRight (u : 1 < c 1) (a : MarkInterior c 2) (h : MarkInterior c 3) (z : MarkInterior c 4)
  | innerLeft (a : c 2 < 0) (u : MarkInterior c 1) (h : MarkInterior c 3) (z : MarkInterior c 4)
  | innerRight (h : 1 < c 3) (u : MarkInterior c 1) (a : MarkInterior c 2) (z : MarkInterior c 4)

theorem mark_interior_iff_not_exterior {q Z : K[X]} {c : Fin 5 → K}
    (M : Moments q Z c) {i : Fin 5} (ni : i ≠ 0) :
    MarkInterior c i ↔ i ∉ exteriorMarkedClocks c := by
  classical
  have cf : i ∈ exteriorMarkedClocks c ↔ c i < 0 ∨ 1 < c i := by
    simp [exteriorMarkedClocks, ni]
  rw [cf]
  constructor
  · intro h bad
    exact bad.elim (not_lt_of_gt h.1) (not_lt_of_gt h.2)
  · intro h
    exact ⟨lt_of_le_of_ne (le_of_not_gt (fun e => h (Or.inl e))) (M.clock_ne_zero ni).symm,
      lt_of_le_of_ne (le_of_not_gt (fun e => h (Or.inr e))) (M.active i).1⟩

private theorem singleton_else_interior {q Z : K[X]} {c : Fin 5 → K}
    (M : Moments q Z c) {i j : Fin 5} (ex : i ∈ exteriorMarkedClocks c)
    (jn : j ≠ 0) (ij : i ≠ j) : MarkInterior c j := by
  classical
  apply (mark_interior_iff_not_exterior M jn).2
  intro bad
  have low : ({i,j} : Finset (Fin 5)) ⊆ exteriorMarkedClocks c := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    exact hk.elim (fun e => e.symm ▸ ex) (fun e => e.symm ▸ bad)
  have ct := Finset.card_le_card low
  simp only [Finset.card_pair ij] at ct
  have hi := M.exterior_count_le_one
  omega

private theorem sole_exterior_earns_three {q Z : K[X]} {c : Fin 5 → K} (M : Moments q Z c)
    {i : Fin 5} (out : i ∈ exteriorMarkedClocks c) :
    HasAlternationsOn q (Set.Ioo (0 : K) 1) 3 := by
  classical
  have left : 0 < (exteriorMarkedClocks c).card := Finset.card_pos.mpr ⟨i, out⟩
  exact M.unit_alternations_of_exterior_count.mono (fun _ hx => hx) (by omega)

theorem no_first_clock_below_zero {q Z : K[X]} {c : Fin 5 → K} (M : Moments q Z c) :
    ¬ c 1 < 0 := by
  intro bad
  have ex : 1 ∈ exteriorMarkedClocks c := by simp [exteriorMarkedClocks, bad]
  have charge := sole_exterior_earns_three M ex
  have ho := (forward_pair_negative_clock M bad).add_open charge bad.le le_rfl zero_le_one
  have cap := ho.le_natDegree
  have up := M.qDegree
  omega

theorem no_last_clock_above_one {q Z : K[X]} {c : Fin 5 → K} (M : Moments q Z c) :
    ¬ 1 < c 4 := by
  intro bad
  have ex : 4 ∈ exteriorMarkedClocks c := by simp [exteriorMarkedClocks, bad]
  have charge := sole_exterior_earns_three M ex
  have ho := charge.add_open (reverse_pair_clock_above_one M bad) zero_le_one le_rfl bad.le
  have cap := ho.le_natDegree
  have up := M.qDegree
  omega

private theorem disjoint_end_four {q Z : K[X]} {c : Fin 5 → K} (M : Moments q Z c)
    (u : MarkInterior c 1) (z : MarkInterior c 4) (sep : c 1 ≤ c 4) :
    HasAlternationsOn q (Set.Ioo (0 : K) 1) 4 :=
  (forward_pair_inside M u.1).add_open (reverse_pair_inside M z.2) u.1.le sep z.2.le

private theorem exterior_signs_of_disjoint {q Z : K[X]} {c : Fin 5 → K} (M : Moments q Z c)
    (monic : q.Monic) (u : MarkInterior c 1) (z : MarkInterior c 4) (sep : c 1 ≤ c 4) :
    (∀ x : K, x ≤ 0 → 0 < q.eval x) ∧ (∀ x : K, 1 ≤ x → 0 < q.eval x) := by
  have dg : q.natDegree = 4 := M.natDegree_eq_four_of_full_packet
  obtain ⟨left,right,_,_⟩ := exterior_of_even_alternations (n := 2) (by decide) monic
    (by simpa using dg) (by simpa using disjoint_end_four M u z sep)
  exact ⟨left,right⟩

private theorem no_disjoint_forward_inner_above_one {q Z : K[X]} {c : Fin 5 → K} (M : Moments q Z c)
    (monic : q.Monic) (u : MarkInterior c 1) (z : MarkInterior c 4) (uz : c 1 < c 4)
    (a : 1 < c 2) : False := by
  obtain ⟨left,right⟩ := exterior_signs_of_disjoint M monic u z uz.le
  obtain ⟨gap,mean⟩ := gap_nonneg_and_right_mean_pos M.qDegree u.1 uz z.2
    (left 0 le_rfl) (right 1 le_rfl) M.forwardFirst M.forwardSecond M.reverseFirst M.reverseSecond
  let F := X*(X-C (c 1))*q
  have fd : F.natDegree ≤ 6 :=
    natDegree_mul_le_of_le (natDegree_mul_le_of_le natDegree_X.le (natDegree_X_sub_C _).le) M.qDegree
  have pay : F.natDegree ≤ 19 := fd.trans (by decide)
  have ev (x : K) : F.eval x = x*(x-c 1)*q.eval x := by simp only [F, eval_mul, eval_sub, eval_X, eval_C]
  have mid : 0 < integral (c 4) 1 F := by
    have alg : F = C (1-c 1)*q - C (2-c 1)*((1-X)*q) + (1-X)^2*q := by
      simp only [F, map_sub, map_one, map_ofNat]
      ring
    rw [alg, map_add, map_sub, integral_C_mul, integral_C_mul, M.reverseFirst, M.reverseSecond,
      mul_zero, sub_zero, add_zero]
    exact mul_pos (sub_pos.mpr u.2) mean
  have leftPart : 0 ≤ integral (c 1) (c 4) F := by
    rw [interval_exact _ _ _ pay]
    apply Finset.sum_nonneg
    intro i _
    have hx := intervalPoint_mem uz i
    rw [ev]
    exact mul_nonneg (intervalWeight_pos uz i).le
      (mul_nonneg (mul_nonneg (u.1.trans hx.1).le (sub_nonneg.mpr hx.1.le))
        (gap _ ⟨hx.1.le, hx.2.le⟩))
  have rightPart : 0 < integral 1 (c 2) F := by
    have pr (i : Fin 19) : 0 < F.eval (intervalPoint 1 (c 2) i) := by
      have hx := intervalPoint_mem a i
      rw [ev]
      exact mul_pos (mul_pos (zero_lt_one.trans hx.1) (sub_pos.mpr (u.2.trans hx.1))) (right _ hx.1.le)
    exact integral_pos_of_grid_samples a pay (fun i => (pr i).le) ⟨0, pr 0⟩
  have s₁ := exact_integral_join F (c 1) (c 4) 1
  have s₂ := exact_integral_join F (c 1) 1 (c 2)
  have zero : integral (c 1) (c 2) F = 0 := forward_genuine_difference M
  linarith only [s₁, s₂, zero, leftPart, mid, rightPart]

theorem no_wrong_direction_forward_inner {q Z : K[X]} {c : Fin 5 → K} (M : Moments q Z c)
    (u : MarkInterior c 1) (z : MarkInterior c 4) : ¬ 1 < c 2 := by
  intro a
  by_cases uz : c 1 < c 4
  · let t := q.leadingCoeff⁻¹
    have tn : t ≠ 0 := inv_ne_zero (leadingCoeff_ne_zero.mpr M.qNonzero)
    exact no_disjoint_forward_inner_above_one (moments_scale_nonzero M tn)
      (monic_mul_leadingCoeff_inv M.qNonzero) u z uz a
  · obtain ⟨A, B, D, A0, B0, D0, eq⟩ := reflected_moments_primitive_balance M
    have lhs := mul_pos (sub_pos.mpr z.2) A0
    have p1 := mul_neg_of_pos_of_neg (sub_pos.mpr u.2) (sub_neg.mpr a)
    have p2 : ((1-c 4)-1)*((1-c 4)-(1-c 1))*((1-c 4)-(1-c 2)) ≤ 0 := by
      apply mul_nonpos_of_nonpos_of_nonneg
      · apply mul_nonpos_of_nonpos_of_nonneg <;> linarith only [z.1, le_of_not_gt uz]
      · linarith only [a,z.2]
    have rhs_nonpos := add_nonpos (mul_neg_of_neg_of_pos p1 B0).le
      (mul_nonpos_of_nonpos_of_nonneg p2 D0.le)
    have lhs_nonpos : (1 - c 4) * A ≤ 0 := by
      rw [eq]
      exact rhs_nonpos
    exact (not_lt_of_ge lhs_nonpos) lhs

theorem no_wrong_direction_reverse_inner {q Z : K[X]} {c : Fin 5 → K} (M : Moments q Z c)
    (u : MarkInterior c 1) (z : MarkInterior c 4) : ¬ c 3 < 0 := by
  intro h
  have uz := M.outer_order_of_negative_reverse_inner u.1 u.2 z.1 h
  let t := q.leadingCoeff⁻¹
  have tn : t ≠ 0 := inv_ne_zero (leadingCoeff_ne_zero.mpr M.qNonzero)
  let p := q*C t
  have mp : p.Monic := monic_mul_leadingCoeff_inv M.qNonzero
  let N : Moments p Z c := moments_scale_nonzero M tn
  have off := (exterior_signs_of_disjoint N mp u z uz.le).2 1 le_rfl
  have n := reflected_moments N off.ne'
  have ui : MarkInterior (mirrorClock c) 1 := ⟨sub_pos.mpr z.2, by
    change 1-c 4 < 1
    linarith only [z.1]⟩
  have zi : MarkInterior (mirrorClock c) 4 := ⟨sub_pos.mpr u.2, by
    change 1-c 1 < 1
    linarith only [u.1]⟩
  apply no_wrong_direction_forward_inner n ui zi
  change 1 < 1-c 3
  linarith only [h]

theorem actual_mark_sector {q Z : K[X]} {c : Fin 5 → K} (M : Moments q Z c) : MarkSector c := by
  classical
  have side {i : Fin 5} (hi : i ≠ 0) (he : i ∈ exteriorMarkedClocks c) : c i < 0 ∨ 1 < c i :=
    (Finset.mem_filter.mp he).2
  by_cases all : AllFourMarksInterior c
  · exact .allInterior all
  · change ¬ (∀ j : Fin 4, c j.succ ∈ Set.Ioo (0 : K) 1) at all
    push_neg at all
    obtain ⟨j, hj⟩ := all
    have ni : j.succ ≠ 0 := by simp
    have out : j.succ ∈ exteriorMarkedClocks c := by
      by_contra none
      exact hj ((mark_interior_iff_not_exterior M ni).2 none)
    fin_cases j
    · change (1 : Fin 5) ∈ exteriorMarkedClocks c at out
      rcases side (by decide) out with bad | good
      · exact (no_first_clock_below_zero M bad).elim
      · exact .outerRight good (singleton_else_interior M out (by decide) (by decide))
          (singleton_else_interior M out (by decide) (by decide))
          (singleton_else_interior M out (by decide) (by decide))
    · change (2 : Fin 5) ∈ exteriorMarkedClocks c at out
      have u : MarkInterior c 1 := singleton_else_interior M out (by decide) (by decide)
      have h : MarkInterior c 3 := singleton_else_interior M out (by decide) (by decide)
      have z : MarkInterior c 4 := singleton_else_interior M out (by decide) (by decide)
      exact (side (by decide) out).elim (fun low => .innerLeft low u h z)
        (fun high => (no_wrong_direction_forward_inner M u z high).elim)
    · change (3 : Fin 5) ∈ exteriorMarkedClocks c at out
      have u : MarkInterior c 1 := singleton_else_interior M out (by decide) (by decide)
      have a : MarkInterior c 2 := singleton_else_interior M out (by decide) (by decide)
      have z : MarkInterior c 4 := singleton_else_interior M out (by decide) (by decide)
      exact (side (by decide) out).elim
        (fun low => (no_wrong_direction_reverse_inner M u z low).elim) (fun high => .innerRight high u a z)
    · change (4 : Fin 5) ∈ exteriorMarkedClocks c at out
      rcases side (by decide) out with good | bad
      · exact .outerLeft good (singleton_else_interior M out (by decide) (by decide))
          (singleton_else_interior M out (by decide) (by decide))
          (singleton_else_interior M out (by decide) (by decide))
      · exact (no_last_clock_above_one M bad).elim

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
