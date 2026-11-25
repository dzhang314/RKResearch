module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorErasureLaw

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Exact local windows of the three-interior packet

The two end pairs force the middle root into the appropriate end ranges.
The inner tests and end pairs jointly pay the *true* difference windows.
All arguments are over the packet's own ordered field and use the finite
positive grid, including when the residual vanishes at an endpoint.
-/
namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

open Polynomial RKCert.ReviewedNative.PositiveRule19 RKCert.ReviewedNative.FiniteOrderedSigns
open RKCert.ReviewedNative.OrderedPolynomialSignStrips
open scoped Polynomial

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem threeInterior_residual_pos {s x : K} (ss : s ∈ Set.Icc 0 1)
    (hx : x ∈ Set.Ioo 0 1) : 0 < (threeInteriorResidual s).eval x := by
  simp only [threeInteriorResidual, eval_add, eval_mul, eval_C, eval_X]
  rcases eq_or_lt_of_le ss.1 with z | p
  · rw [← z, sub_zero, one_mul, zero_add]
    exact hx.1
  · exact add_pos_of_pos_of_nonneg p (mul_nonneg (sub_nonneg.mpr ss.2) hx.1.le)

theorem threeInterior_residual_degree (s : K) : (threeInteriorResidual s).natDegree ≤ 1 := by
  unfold threeInteriorResidual
  exact natDegree_add_le_of_le ((natDegree_C s).trans_le (Nat.zero_le 1))
    ((natDegree_C_mul_le _ _).trans natDegree_X.le)

theorem threeInterior_profile_degree (s : K) (r : Fin 3 → K) :
    (threeInteriorProfile s r).natDegree ≤ 4 := by
  unfold threeInteriorProfile
  have h : (indexedHull r Finset.univ).natDegree ≤ 3 := by
    simp only [indexedHull_degree, Finset.card_univ, Fintype.card_fin, le_refl]
  exact natDegree_mul_le_of_le (threeInterior_residual_degree s) h

theorem threeInterior_erased_degree (s : K) (r : Fin 3 → K) (e : K) :
    (threeInteriorErasedProfile s r e).natDegree ≤ 5 := by
  unfold threeInteriorErasedProfile
  exact natDegree_mul_le_of_le (natDegree_X_sub_C e).le (threeInterior_profile_degree s r)

theorem threeInterior_profile_eval (s : K) (r : Fin 3 → K) (x : K) :
    (threeInteriorProfile s r).eval x =
      (threeInteriorResidual s).eval x * ((x-r 0)*(x-r 1)*(x-r 2)) := by
  simp only [threeInteriorProfile, threeInterior_hull_three, eval_mul, eval_sub, eval_X, eval_C]

theorem threeInterior_erased_eval (s : K) (r : Fin 3 → K) (e x : K) :
    (threeInteriorErasedProfile s r e).eval x =
      (x-e) * ((threeInteriorResidual s).eval x * ((x-r 0)*(x-r 1)*(x-r 2))) := by
  simp only [threeInteriorErasedProfile, eval_mul, eval_sub, eval_X, eval_C, threeInterior_profile_eval]

private theorem no_zero_of_paid_square {a l u : K} (lu : l < u) {P : K[X]} (pd : P.natDegree ≤ 19)
    (V : K → K) (vp : ∀ x ∈ Set.Ioo l u, 0 < V x)
    (shape : ∀ x ∈ Set.Ioo l u, P.eval x = V x*(x-a)^2)
    (zero : integral l u P = 0) : False := by
  obtain ⟨i, hi⟩ := exists_nonzero_grid_sample lu (X_sub_C_ne_zero a)
    (by rw [natDegree_X_sub_C]; decide)
  have live : intervalPoint l u i-a ≠ 0 := by simpa only [eval_sub,eval_X,eval_C] using hi
  have pos := integral_pos_of_grid_samples lu pd
    (fun j => by
      rw [shape _ (intervalPoint_mem lu j)]
      exact mul_nonneg (vp _ (intervalPoint_mem lu j)).le (sq_nonneg _))
    ⟨i,by
      rw [shape _ (intervalPoint_mem lu i)]
      exact mul_pos (vp _ (intervalPoint_mem lu i)) (sq_pos_of_ne_zero live)⟩
  exact (ne_of_gt pos) zero

theorem ThreeInteriorNormalized.left_middle_root {s : K} {r : Fin 3 → K} {m : Fin 4 → K}
    (H : ThreeInteriorNormalized s r m) : r 1 < m 0 := by
  by_contra! bound
  let P : K[X] := X*threeInteriorErasedProfile s r (r 0)
  let V (x : K) := x*(threeInteriorResidual s).eval x*((x-r 1)*(x-r 2))
  have deg : P.natDegree ≤ 19 :=
    (natDegree_mul_le_of_le natDegree_X.le (threeInterior_erased_degree s r (r 0))).trans (by decide)
  apply no_zero_of_paid_square (a := r 0) (H.markInside 0).1 deg V
  · intro x hx
    have one : x < 1 := hx.2.trans (H.markInside 0).2
    have h1 : x < r 1 := hx.2.trans_le bound
    have h2 : x < r 2 := h1.trans (H.rootOrder (by decide : (1 : Fin 3) < 2))
    exact mul_pos (mul_pos hx.1 (threeInterior_residual_pos ⟨H.parameter.1,H.parameter.2.le⟩ ⟨hx.1,one⟩))
      (mul_pos_of_neg_of_neg (sub_neg.mpr h1) (sub_neg.mpr h2))
  · intro x _
    simp only [P,V,eval_mul,eval_X,threeInterior_erased_eval]
    ring
  · exact H.stops.erase_left_outer (r 0)

theorem ThreeInteriorNormalized.right_middle_root {s : K} {r : Fin 3 → K} {m : Fin 4 → K}
    (H : ThreeInteriorNormalized s r m) : m 3 < r 1 := by
  by_contra! bound
  let P : K[X] := (1-X)*threeInteriorErasedProfile s r (r 2)
  let V (x : K) := (1-x)*(threeInteriorResidual s).eval x*((x-r 0)*(x-r 1))
  have deg : P.natDegree ≤ 19 :=
    (natDegree_mul_le_of_le (unit_right_weight_degree (K := K)).le
      (threeInterior_erased_degree s r (r 2))).trans (by decide)
  apply no_zero_of_paid_square (a := r 2) (H.markInside 3).2 deg V
  · intro x hx
    have x0 : 0 < x := (H.markInside 3).1.trans hx.1
    have h1 : r 1 < x := bound.trans_lt hx.1
    have h0 : r 0 < x := (H.rootOrder (by decide : (0 : Fin 3) < 1)).trans h1
    exact mul_pos (mul_pos (sub_pos.mpr hx.2)
      (threeInterior_residual_pos ⟨H.parameter.1,H.parameter.2.le⟩ ⟨x0,hx.2⟩))
      (mul_pos (sub_pos.mpr h0) (sub_pos.mpr h1))
  · intro x _
    simp only [P,V,eval_mul,eval_X,eval_sub,eval_one,threeInterior_erased_eval]
    ring
  · exact H.stops.erase_right_outer (r 2)

private theorem same_side_factor {l u e x t : K} (hx : x ∈ Set.Ioo l u)
    (ht : t ∈ Set.Ioo l u) (side : e ≤ l ∨ u ≤ e) : 0 < (t-e)*(x-e) := by
  rcases side with lo | hi
  · exact mul_pos (sub_pos.mpr (lo.trans_lt ht.1)) (sub_pos.mpr (lo.trans_lt hx.1))
  · exact mul_pos_of_neg_of_neg (sub_neg.mpr (ht.2.trans_le hi)) (sub_neg.mpr (hx.2.trans_le hi))

/-- A paid erased test on an open genuine window forces an actual interior
root of the un-erased profile. The erased mark lies outside that window. -/
theorem threeInterior_root_between_of_erased_paid {s e l u : K} {r : Fin 3 → K} {A : K[X]}
    (ss : s ∈ Set.Icc 0 1) (l0 : 0 ≤ l) (lu : l < u) (u1 : u ≤ 1)
    (outside : e ≤ l ∨ u ≤ e) (ad : A.natDegree ≤ 1)
    (ap : ∀ x ∈ Set.Ioo l u, 0 < A.eval x)
    (zero : integral l u (A*threeInteriorErasedProfile s r e) = 0) :
    ∃ i : Fin 3, r i ∈ Set.Ioo l u := by
  by_contra h
  have out (i : Fin 3) : r i ≤ l ∨ u ≤ r i := by
    by_cases li : l < r i
    · exact Or.inr (le_of_not_gt fun iu => h ⟨i,li,iu⟩)
    · exact Or.inl (le_of_not_gt li)
  let t : K := (l+u)/2
  have ht : t ∈ Set.Ioo l u := ⟨by dsimp [t]; linarith, by dsimp [t]; linarith⟩
  let E := threeInteriorErasedProfile s r e
  let P := C (E.eval t)*(A*E)
  have pd : P.natDegree ≤ 19 :=
    ((natDegree_C_mul_le _ _).trans
      (natDegree_mul_le_of_le ad (threeInterior_erased_degree s r e))).trans (by decide)
  have in_unit {x : K} (hx : x ∈ Set.Ioo l u) : x ∈ Set.Ioo (0:K) 1 :=
    ⟨l0.trans_lt hx.1, hx.2.trans_le u1⟩
  have strict (x : K) (hx : x ∈ Set.Ioo l u) : 0 < P.eval x := by
    have sh : P.eval x =
        A.eval x *
        ((threeInteriorResidual s).eval t*(threeInteriorResidual s).eval x) *
        ((t-e)*(x-e))*((t-r 0)*(x-r 0))*((t-r 1)*(x-r 1))*((t-r 2)*(x-r 2)) := by
      simp only [P,E,eval_mul,eval_C,threeInterior_erased_eval]
      ring
    rw [sh]
    exact mul_pos (mul_pos (mul_pos (mul_pos (mul_pos (ap x hx)
      (mul_pos (threeInterior_residual_pos ss (in_unit ht)) (threeInterior_residual_pos ss (in_unit hx))))
      (same_side_factor hx ht outside)) (same_side_factor hx ht (out 0)))
      (same_side_factor hx ht (out 1))) (same_side_factor hx ht (out 2))
  have gg (j : Fin 19) := strict _ (intervalPoint_mem lu j)
  have hp := integral_pos_of_grid_samples lu pd (fun j => (gg j).le) ⟨0,gg 0⟩
  have pzero : integral l u P = 0 := by
    change integral l u (C (E.eval t)*(A*E)) = 0
    rw [threeInterior_integral_C_mul, show integral l u (A*E) = 0 from zero, mul_zero]
  exact (ne_of_gt hp) pzero

/-- Precise ordinal data used by the published local-window reduction.
The two inner alternatives include both paid genuine difference windows. -/
structure ThreeInteriorRootWindows (r : Fin 3 → K) (m : Fin 4 → K) : Prop where
  leftPair : r 1 < m 0
  rightPair : m 3 < r 1
  leftInner : (∃ i, m 0 < r i ∧ r i < m 1) ∨
    ((∃ i, r i < m 1) ∧ ∃ i, m 1 < r i ∧ r i < m 0)
  rightInner : (∃ i, m 2 < r i ∧ r i < m 3) ∨
    ((∃ i, m 2 < r i) ∧ ∃ i, m 3 < r i ∧ r i < m 2)

theorem ThreeInteriorNormalized.local_windows {s : K} {r : Fin 3 → K} {m : Fin 4 → K}
    (H : ThreeInteriorNormalized s r m) : ThreeInteriorRootWindows r m := by
  have ss : s ∈ Set.Icc (0:K) 1 := ⟨H.parameter.1,H.parameter.2.le⟩
  let L : K[X] := X*threeInteriorErasedProfile s r (m 0)
  let R : K[X] := (1-X)*threeInteriorErasedProfile s r (m 3)
  have l0 : integral 0 (m 0) L = 0 := H.stops.erase_left_outer (m 0)
  have la : integral 0 (m 1) L = 0 := H.stops.erase_left_inner
  have r3 : integral (m 3) 1 R = 0 := H.stops.erase_right_outer (m 3)
  have rh : integral (m 2) 1 R = 0 := H.stops.erase_right_inner
  have ld : integral (m 0) (m 1) L = 0 := by
    have j := exact_integral_join L 0 (m 0) (m 1)
    rwa [l0, la, zero_add] at j
  have rd : integral (m 2) (m 3) R = 0 := by
    have j := exact_integral_join R (m 2) (m 3) 1
    rwa [r3, rh, add_zero] at j
  have lroot {l u : K} (hl : 0 ≤ l) (lu : l < u) (hu : u ≤ 1)
      (out : m 0 ≤ l ∨ u ≤ m 0) (paid : integral l u L = 0) :
      ∃ i : Fin 3, r i ∈ Set.Ioo l u :=
    threeInterior_root_between_of_erased_paid ss hl lu hu out natDegree_X.le
      (fun x hx => by rw [eval_X]; exact hl.trans_lt hx.1) paid
  have rroot {l u : K} (hl : 0 ≤ l) (lu : l < u) (hu : u ≤ 1)
      (out : m 3 ≤ l ∨ u ≤ m 3) (paid : integral l u R = 0) :
      ∃ i : Fin 3, r i ∈ Set.Ioo l u :=
    threeInterior_root_between_of_erased_paid ss hl lu hu out (unit_right_weight_degree (K := K)).le
      (fun x hx => by
        rw [eval_sub,eval_one,eval_X]
        exact sub_pos.mpr (hx.2.trans_le hu)) paid
  refine ⟨H.left_middle_root,H.right_middle_root,?_,?_⟩
  · rcases lt_or_gt_of_ne (fun eq : m 0 = m 1 => (by decide : (0 : Fin 4) ≠ 1) (H.markDistinct eq)) with lt | lt
    · exact Or.inl (lroot (H.markInside 0).1.le lt (H.markInside 1).2.le (Or.inl le_rfl) ld)
    · have rev : integral (m 1) (m 0) L = 0 := by
        rw [exact_integral_reverse L (m 0) (m 1), ld, neg_zero]
      obtain ⟨i, hi⟩ := lroot le_rfl (H.markInside 1).1 (H.markInside 1).2.le (Or.inr lt.le) la
      exact Or.inr ⟨⟨i,hi.2⟩, lroot (H.markInside 1).1.le lt (H.markInside 0).2.le (Or.inr le_rfl) rev⟩
  · rcases lt_or_gt_of_ne (fun eq : m 2 = m 3 => (by decide : (2 : Fin 4) ≠ 3) (H.markDistinct eq)) with lt | lt
    · exact Or.inl (rroot (H.markInside 2).1.le lt (H.markInside 3).2.le (Or.inr le_rfl) rd)
    · have rev : integral (m 3) (m 2) R = 0 := by
        rw [exact_integral_reverse R (m 2) (m 3), rd, neg_zero]
      obtain ⟨i, hi⟩ := rroot (H.markInside 2).1.le (H.markInside 2).2 le_rfl (Or.inl lt.le) rh
      exact Or.inr ⟨⟨i,hi.1⟩, rroot (H.markInside 3).1.le lt (H.markInside 2).2.le (Or.inl le_rfl) rev⟩

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
