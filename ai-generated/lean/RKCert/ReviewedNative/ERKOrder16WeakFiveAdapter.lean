module

public import RKCert.ReviewedNative.ERKOrder16WeakHead
public import RKCert.ReviewedNative.ERKOrder16WeakFiveMoments
public import RKCert.ReviewedNative.GuardedGroupedMoments

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # All twelve scalar moments from the actual weak-five mask

This is only the physical extraction. It does not split the ordinary
weak head into four or five sites and does not exclude either branch.
-/
namespace RKResearch.Certified.ERK16

open RKResearch Polynomial Module
open RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse
open RKResearch.Certified.Graded.Reverse.Thin
open RKCert.Endpoint RKCert.Endpoint.WeightedClock
open RKCert.ReviewedNative.PositiveRule19
open RKCert.ReviewedNative.FiniteOrderedSigns RKCert.ReviewedNative.WeakFive16
open scoped BigOperators Classical Matrix

noncomputable section

section Algebraic

variable {K : Type*} [Field K] [CharZero K]
variable {A : Matrix (Fin 24) (Fin 24) K} {b θ : Fin 24 → K}
variable {q Q P : K[X]}

private theorem weak_five_reflect_back (W : WeakFivePaidMask A b q Q P θ) :
    q.comp (1-X) = Q := by
  letI : Infinite K := Infinite.of_injective (Nat.cast : ℕ → K) Nat.cast_injective
  apply Polynomial.funext
  intro x
  rw [eval_comp, eval_sub, eval_one, eval_X, W.reflected, sub_sub_cancel]

/-- The checked reverse contrast law, written in the original forward
clock. Its maximum test degree is exactly ten in the weak-five chart. -/
theorem WeakFivePaidMask.forward_contrast_mass
    (W : WeakFivePaidMask A b q Q P θ) (ho : HasOrder 16 A b)
    (S : K[X]) (sd : S.natDegree ≤ 10) :
    integral 0 1 ((1-X) * q * S) =
      ∑ i, reverseContrast A b Q P i * S.eval (nodes A i) := by
  let R := S.comp (1-X)
  have rd : R.natDegree ≤ 10 :=
    natDegree_comp_le.trans (by rw [one_sub_X_natDegree, mul_one]; exact sd)
  have mass := reverse_contrast_moment ho Q P R
    (by have := W.reverseDegree; omega) (by have := W.otherDegree; omega)
  have poly : (((1-X) * q * S).comp (1-X)) = R * (X * Q) := by
    simp only [R, mul_comp, sub_comp, one_comp, X_comp, sub_sub_cancel,
      weak_five_reflect_back W] <;> ac_rfl
  have ev (i : Fin 24) : R.eval (reflectedClock A i) = S.eval (nodes A i) := by
    have flip : (1-X : K[X]).eval (reflectedClock A i) = nodes A i := by
      simp only [eval_sub, eval_one, eval_X]
      change 1-(1-nodes A i) = nodes A i
      exact sub_sub_cancel _ _
    change (S.comp (1-X)).eval (reflectedClock A i) = _
    rw [eval_comp, flip]
  rw [← integral_reflect ((1-X) * q * S) (0 : K), sub_zero, poly,
    integral_zero_left, formalPrimitive_eq_native, ← mass]
  apply Finset.sum_congr rfl
  intro i _
  rw [weightedEval_apply, ev i]
  exact mul_comm _ _

/-- Multiplying the true moment by X kills the actual origin clock.
The remaining grouped law is still exact through degree nine. -/
theorem WeakFivePaidMask.guarded_grouped_moments [DecidableEq K]
    (W : WeakFivePaidMask A b q Q P θ) (ho : HasOrder 16 A b) :
    GroupedUnitMoments (X * (1-X)) q
      (((weakFiveRows A b Q P).image (nodes A)).erase 0)
      (fun r => r * (∑ i ∈ (weakFiveRows A b Q P).filter (fun j => nodes A j = r),
        reverseContrast A b Q P i)) 9 := by
  let c := nodes A
  let v := reverseContrast A b Q P
  let V := weakFiveRows A b Q P
  let S := V.image c
  let μ (r : K) : K := r * (∑ i ∈ V.filter (fun j => c j = r), v i)
  intro H hd
  have xh : (X * H).natDegree ≤ 10 := by
    exact natDegree_mul_le_of_le (show (X : K[X]).natDegree ≤ 1 from natDegree_X.le) hd
  change integral 0 1 ((X * (1-X)) * q * H) =
    ∑ r ∈ S.erase 0, μ r * H.eval r
  calc
    integral 0 1 ((X * (1-X)) * q * H) =
        integral 0 1 ((1-X) * q * (X * H)) := by
      congr 1 <;> ac_rfl
    _ = ∑ i, v i * (X * H).eval (c i) := W.forward_contrast_mass ho (X * H) xh
    _ = ∑ i ∈ V, v i * (X * H).eval (c i) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ V)
      intro i _ hi
      have off : v i = 0 := by
        by_contra nz
        exact hi ((mem_weakFiveRows i).mpr nz)
      rw [off, zero_mul]
    _ = ∑ r ∈ S, ∑ i ∈ V.filter (fun j => c j = r),
          v i * (X * H).eval (c i) :=
      (Finset.sum_fiberwise_of_maps_to (s := V) (t := S) (g := c)
        (fun i hi => Finset.mem_image_of_mem c hi)
        (fun i => v i * (X * H).eval (c i))).symm
    _ = ∑ r ∈ S, μ r * H.eval r := by
      apply Finset.sum_congr rfl
      intro r _
      dsimp only [μ]
      conv_rhs => rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
      simp only [eval_mul, eval_X] <;> ac_rfl
    _ = ∑ r ∈ S.erase 0, μ r * H.eval r := by
      symm
      apply Finset.sum_subset (Finset.erase_subset 0 S)
      intro r hr off
      have rz : r = 0 := by
        by_contra nz
        exact off (Finset.mem_erase.mpr ⟨nz, hr⟩)
      rw [rz]
      simp only [μ, zero_mul]

end Algebraic

section Ordered

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A : Matrix (Fin 24) (Fin 24) K} {b θ : Fin 24 → K}
variable {q Q P Z : K[X]}

set_option maxHeartbeats 900000 in
/-- Add the original left and right end tests to the two paid chronological
inner ports, and use the exact actual nodal factor to recover all six
global moments. The labels are not put in numerical order. -/
theorem WeakFivePaidMask.full_moments
    (W : WeakFivePaidMask A b q Q P θ)
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 16 A b)
    {ι : Fin 5 → Fin 24} (B : WeakFiveInnerPorts A b q Q P Z ι) :
    Moments q Z (fun k => nodes A (ι k)) := by
  let : DecidableEq K := fun x y => Classical.propDecidable (x = y)
  let c (k : Fin 5) := nodes A (ι k)
  let V := weakFiveRows A b Q P
  let S := V.image (nodes A)
  let T := S.erase 0
  have member (k : Fin 5) : ι k ∈ V := (B.rows _).mpr ⟨k, rfl⟩
  have c0 : c 0 = 0 := by
    change nodes A (ι 0) = 0
    rw [B.origin]
    change (∑ j, A 0 j * (1 : K)) = 0
    exact Finset.sum_eq_zero fun j _ => by rw [ha 0 j (Fin.zero_le j), zero_mul]
  have simple : Function.Injective c := by
    intro i j e
    exact B.increasing.injective (W.clockSimple (member i) (member j) e)
  have active (i : Fin 5) : c i ≠ 1 ∧ q.eval (c i) ≠ 0 := by
    have live := W.active (member i)
    constructor
    · intro e
      apply live.2.1
      change 1-c i = 0
      rw [e, sub_self]
    · rw [W.reflected]
      exact live.2.2.2
  have qn : q ≠ 0 := fun e => (active 0).2 (by rw [e, eval_zero])
  have middle : Z = (X - C (c 2)) * (X - C (c 3)) := by
    have aD : X - C (c 2) ∣ Z := dvd_iff_isRoot.mpr
      ((B.middleRoots (c 2)).mpr (Or.inl rfl))
    have hD : X - C (c 3) ∣ Z := dvd_iff_isRoot.mpr
      ((B.middleRoots (c 3)).mpr (Or.inr rfl))
    have cop : IsCoprime (X - C (c 2)) (X - C (c 3)) :=
      isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr B.different).isUnit
    refine eq_of_monic_of_dvd_of_natDegree_le
      ((monic_X_sub_C _).mul (monic_X_sub_C _)) B.monic (cop.mul_dvd aD hD) ?_
    rw [B.degree, natDegree_mul (X_sub_C_ne_zero (c 2)) (X_sub_C_ne_zero (c 3)),
      natDegree_X_sub_C (c 2), natDegree_X_sub_C (c 3)]
  have onlyOrigin (R : K[X]) (at0 : R.eval 0 = 0) :
      ∀ j, j < ι 1 → j ∈ V → R.eval (nodes A j) = 0 := by
    intro j hj hV
    obtain ⟨k, rfl⟩ := (B.rows j).mp hV
    have hk : k < (1 : Fin 5) := B.increasing.lt_iff_lt.mp hj
    change k.val < 1 at hk
    have k0 : k = 0 := Fin.ext (by change k.val = 0; omega)
    rw [k0]
    change R.eval (c 0) = 0
    rw [c0]
    exact at0
  have last (R : K[X]) (rd : R.natDegree ≤ 1) :
      (primitive (R * (X * Q))).eval (reflectedClock A (ι 4)) = 0 := by
    apply W.reverse_suffix ha ho (width24_paid_frame ha ho)
      (width24_quadratic_cover ha ho).supports R rd (member 4)
    intro j hj hV
    obtain ⟨k, rfl⟩ := (B.rows j).mp hV
    have hk : (4 : Fin 5) < k := B.increasing.lt_iff_lt.mp hj
    change 4 < k.val at hk
    have lt := k.isLt
    omega
  have rightOf {R F : K[X]} {i : Fin 24}
      (shape : F.comp (1-X) = R * (X * Q))
      (paid : (primitive (R * (X * Q))).eval (reflectedClock A i) = 0) :
      integral (nodes A i) 1 F = 0 := by
    rw [← integral_reflect F (nodes A i), integral_zero_left, formalPrimitive_eq_native, shape]
    exact paid
  have zeroSite : (0 : K) ∈ S := Finset.mem_image.mpr ⟨ι 0, member 0, c0⟩
  have sCard : S.card = 5 := (Finset.card_image_iff.mpr W.clockSimple).trans W.count
  have tCard : T.card = 4 := by
    dsimp only [T]
    rw [Finset.card_erase_of_mem zeroSite, sCard] <;> decide
  have split : nodalHull S = X * nodalHull T := by
    have e := (Finset.mul_prod_erase S (fun r => (X - C r : K[X])) zeroSite).symm
    change (∏ x ∈ S, (X - C x : K[X])) = (X - C 0) * ∏ x ∈ S.erase 0, (X - C x) at e
    rw [map_zero, sub_zero] at e
    exact e
  have tail : nodalHull T = nodalTail c Z := by
    apply mul_left_cancel₀ X_ne_zero
    calc
      X * nodalHull T = nodalHull S := split.symm
      _ = X * nodalTail c Z := by
        simpa only [nodalTail, mul_assoc] using B.supportFactor
  change Moments q Z c
  refine ⟨qn, W.forwardDegree, c0, simple, active, middle, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [integral_zero_left, formalPrimitive_eq_native]
    exact W.forward_prefix ha ho X (by rw [natDegree_X] <;> decide)
      (member 1) (onlyOrigin X (by simp))
  · rw [integral_zero_left, formalPrimitive_eq_native]
    exact W.forward_prefix ha ho (X^2) (by rw [natDegree_X_pow])
      (member 1) (onlyOrigin (X^2) (by simp))
  · rw [integral_zero_left, formalPrimitive_eq_native]
    exact B.forwardInner
  · refine rightOf (i := ι 4) (R := 1) ?_ (last 1 (by simp))
    simp only [mul_comp, sub_comp, one_comp, X_comp, sub_sub_cancel,
      weak_five_reflect_back W, one_mul]
  · refine rightOf (i := ι 4) (R := X) ?_ (last X natDegree_X.le)
    simp only [mul_comp, pow_comp, sub_comp, one_comp, X_comp, sub_sub_cancel,
      weak_five_reflect_back W, pow_two, mul_assoc]
  · let R : K[X] := X - C (reflectedClock A (ι 4))
    have refl : ((C (c 4) - X : K[X]).comp (1-X)) = R := by
      rw [sub_comp, C_comp, X_comp]
      change C (c 4) - (1-X) = X - C (1-c 4)
      rw [map_sub, map_one]
      ring
    have shape : (((1-X) * (C (c 4) - X) * q).comp (1-X)) = R * (X * Q) := by
      rw [mul_comp, mul_comp, refl, weak_five_reflect_back W]
      simp only [sub_comp, one_comp, X_comp, sub_sub_cancel] <;> ac_rfl
    exact rightOf (i := ι 3) shape B.reverseInner
  · intro H hd
    have room : T.card + 5 ≤ 9 := by rw [tCard] <;> decide
    have paid := (W.guarded_grouped_moments ho).nodal_orthogonality room H hd
    change integral 0 1 ((X * (1-X)) * (q * nodalHull T) * H) = 0 at paid
    rwa [tail] at paid

/-- The existing five-site census supplies the full scalar input on
ordinary rank seven. The premise is the separate five-site branch. -/
theorem width24_weak_five_moments_of_ordinary_head
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 16 A b)
    (seven : finrank K (zeroSpace A 7) = 7)
    {U : Submodule K (Fin 24 → K)} {w : Fin 24 → K}
    (L : Width24OrdinaryWeakHead A b U w Q P)
    (five : 5 ≤ (weightedSites (reflectedClock A) (reverseContrast A b Q P)).card) :
    ∃ (q Z : K[X]) (c : Fin 5 → K), Moments q Z c := by
  have C := (width24_weak_five_census ha ho seven L.flat L.coreInside five
    L.qDegree L.pDegree L.qFit L.pFit).2.2.2.2.2
  obtain ⟨q, θ, W, _, _⟩ := actual_weak_five_paid_mask ha ho C
  obtain ⟨ι, Z, B⟩ := width24_weak_five_true_inner_ports ha ho W
  exact ⟨q, Z, fun k => nodes A (ι k), W.full_moments ha ho B⟩

end Ordered

end

end RKResearch.Certified.ERK16
