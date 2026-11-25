module

public import RKCert.ReviewedNative.WeakFiveAlternatingRootBridge
public import RKCert.ReviewedNative.ERKOrder16WeakFiveLowDegree
public import RKCert.ReviewedNative.OrderedPolynomialStripFactors
public import RKCert.ReviewedNative.PolynomialCertificateWeakFiveFourRootExtension

import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Exact quartic root modes on the actual all-interior weak-five packet

The four-change cutoff now consumes all witnessed alternations, not an
assumed tuple of base-field roots. For three changes a real affine residual
is forced and must be noninterior; endpoints are explicitly allowed.
The complementary two-change mode rules out a third change in *every*
ordered extension of the current universe, not only the original field.
-/

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

open Polynomial
open RKCert.ReviewedNative.WeakFive16
open RKCert.ReviewedNative.FiniteOrderedSigns
open RKCert.ReviewedNative.OrderedRootGapSaturation
open RKCert.ReviewedNative.OrderedPolynomialSignStrips
open scoped Polynomial BigOperators

universe u
variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

abbrev AllFourMarksInterior (c : Fin 5 → K) : Prop :=
  ∀ j : Fin 4, c j.succ ∈ Set.Ioo 0 1

theorem map_interior_marks {c : Fin 5 → K} (E : OrderedExtension K)
    (marks : AllFourMarksInterior c) : AllFourMarksInterior (fun i => E.embed (c i)) := by
  intro j
  exact ⟨by simpa only [map_zero] using E.mono (marks j).1,
    by simpa only [map_one] using E.mono (marks j).2⟩

theorem no_four_paid_unit_alternations {q Z : K[X]} {c : Fin 5 → K} (M : Moments q Z c)
    (marks : AllFourMarksInterior c) :
    ¬ HasAlternationsOn q (Set.Ioo (0 : K) 1) 4 := by
  intro h
  obtain ⟨E, r, ord, inner, roots⟩ := roots_of_paid_unit_alternations (by decide) h
  exact no_four_interior_roots_in_ordered_extension M E.embed E.mono marks ord.injective inner roots

/-- Positive after multiplying by a fixed nonzero sign, including
the seam where the extra root is 0 or 1. The packet retains its own q. -/
structure ThreeChangeLayout (q : K[X]) (r : Fin 3 → K) (e : K) : Prop where
  sorted : StrictMono r
  unit : ∀ i, r i ∈ Set.Ioo 0 1
  outside : e ≤ 0 ∨ 1 ≤ e
  factor : q = C q.leadingCoeff * ((X - C e) * indexedHull r Finset.univ)

theorem ThreeChangeLayout.positive_residual {q : K[X]} {r : Fin 3 → K} {e : K}
    (H : ThreeChangeLayout q r e) :
    ∃ B : K[X], B.natDegree = 1 ∧ (∀ x ∈ Set.Ioo (0 : K) 1, 0 < B.eval x) ∧
      (q = C q.leadingCoeff * (B * indexedHull r Finset.univ) ∨
        q = -C q.leadingCoeff * (B * indexedHull r Finset.univ)) := by
  rcases H.outside with low | high
  · refine ⟨X - C e, natDegree_X_sub_C _, ?_, Or.inl H.factor⟩
    intro x hx
    simpa only [eval_sub, eval_X, eval_C] using sub_pos.mpr (low.trans_lt hx.1)
  · refine ⟨C e - X, ?_, ?_, Or.inr ?_⟩
    · rw [← neg_sub, natDegree_neg, natDegree_X_sub_C]
    · intro x hx
      simpa only [eval_sub, eval_X, eval_C] using sub_pos.mpr (hx.2.trans_le high)
    · calc q = C q.leadingCoeff * ((X-C e)*indexedHull r Finset.univ) := H.factor
           _ = -C q.leadingCoeff * ((C e-X)*indexedHull r Finset.univ) := by ring

/-- Three real changes fill three unit gaps. If the fourth factor repeated
one of these, a square could be removed without removing any variation;
if it were any other unit root, the already checked four-root sector applies. -/
theorem three_change_layout_in_extension {q Z : K[X]} {c : Fin 5 → K}
    (M : Moments q Z c) (marks : AllFourMarksInterior c)
    (alt : HasAlternationsOn q (Set.Ioo (0 : K) 1) 3) :
    ∃ E : OrderedExtension K, ∃ (r : Fin 3 → E.carrier) (e : E.carrier),
      ThreeChangeLayout (q.map E.embed) r e := by
  classical
  obtain ⟨E, r, ord, unit, qr⟩ := roots_of_paid_unit_alternations (by decide) alt
  let p := q.map E.embed
  have deg : p.natDegree = 4 := (natDegree_map_eq_of_injective E.embed.injective q).trans
    M.natDegree_eq_four_of_full_packet
  obtain ⟨e, factor⟩ := exists_indexed_linear_residual (t := r) (S := Finset.univ)
    (by simpa only [Finset.card_univ, Fintype.card_fin] using deg) ord.injective (fun i _ => qr i)
  have actual : HasAlternationsOn p (Set.Ioo (0 : E.carrier) 1) 3 :=
    alternations_map_unit E.embed E.mono alt
  have distinct (i : Fin 3) : e ≠ r i := by
    intro same
    let S : Finset (Fin 3) := Finset.univ
    let R := C p.leadingCoeff * indexedHull r (S.erase i)
    have sh : indexedHull r S = (X - C (r i)) * indexedHull r (S.erase i) := by
      unfold indexedHull
      exact (Finset.mul_prod_erase S (fun j => X-C (r j)) (Finset.mem_univ i)).symm
    have square : p = R * (X - C (r i))^2 := by
      have hf : p = C p.leadingCoeff * ((X - C e) * indexedHull r S) := factor
      rw [hf, same, sh]
      dsimp only [R]
      ring
    have rd : R.natDegree ≤ 2 := by
      apply (natDegree_C_mul_le _ _).trans
      rw [indexedHull_degree, Finset.card_erase_of_mem (Finset.mem_univ i)]
      simp [S]
    rw [square] at actual
    have impossible := actual.of_mul_sq.le_natDegree
    omega
  have eroot : p.IsRoot e := by
    change (q.map E.embed).eval e = 0
    rw [factor]
    simp [eval_mul, eval_sub, eval_X, eval_C]
  have noInner : ¬ e ∈ Set.Ioo (0 : E.carrier) 1 := by
    intro ei
    let f := withExtra r e
    let roots4 : Fin 4 → E.carrier := f ∘ finSuccEquiv 3
    have inj : Function.Injective roots4 :=
      (withExtra_injective ord.injective distinct).comp (finSuccEquiv 3).injective
    have inside (j : Fin 4) : roots4 j ∈ Set.Ioo 0 1 := by
      change f (finSuccEquiv 3 j) ∈ _
      cases finSuccEquiv 3 j with
      | none => exact ei
      | some k => exact unit k
    have zero (j : Fin 4) : p.IsRoot (roots4 j) := by
      change p.IsRoot (f (finSuccEquiv 3 j))
      cases finSuccEquiv 3 j with
      | none => exact eroot
      | some k => exact qr k
    exact no_four_interior_roots_in_ordered_extension M E.embed E.mono marks inj inside zero
  refine ⟨E, r, e, ⟨ord, unit, ?_, factor⟩⟩
  exact (not_and_or.mp noInner).imp le_of_not_gt le_of_not_gt

theorem layout_map_eq {Z : K[X]} (E : OrderedExtension K) (F : OrderedExtension E.carrier) :
    (Z.map E.embed).map F.embed = Z.map (followedBy E F).embed := by simp [followedBy, map_map]

/-- Either actual three-change data are present in an ordered extension,
or every ordered extension has at most two unit sign alternations.
Four-change inputs have been excluded without any new premise. -/
theorem all_interior_root_modes {q Z : K[X]} {c : Fin 5 → K} (M : Moments q Z c)
    (marks : AllFourMarksInterior c) :
    (∃ E : OrderedExtension K, ∃ (r : Fin 3 → E.carrier) (e : E.carrier),
      ThreeChangeLayout (q.map E.embed) r e) ∨
    (∀ E : OrderedExtension K, ¬ HasAlternationsOn (q.map E.embed) (Set.Ioo 0 1) 3) := by
  classical
  by_cases three : ∃ E : OrderedExtension K, HasAlternationsOn (q.map E.embed) (Set.Ioo 0 1) 3
  · left
    obtain ⟨E, alt⟩ := three
    obtain ⟨F, r, e, layout⟩ :=
      three_change_layout_in_extension (moments_along_field E.embed M) (map_interior_marks E marks) alt
    exact ⟨followedBy E F, r, e, by rwa [← layout_map_eq E F]⟩
  · right
    intro E h
    exact three ⟨E, h⟩

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
