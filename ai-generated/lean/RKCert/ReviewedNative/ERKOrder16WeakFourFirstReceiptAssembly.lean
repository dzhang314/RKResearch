module

public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstVietaReceipts
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

@[expose] public section

/-! # One reflected checker for all four weak-four first-stop families

Every primitive input is fixed rational data; validity is a finite Boolean
check. The result uses the complete chart, all allowed subsets, and all
corners, not any sampled physical tableau or clock.
-/
namespace RKCert.ReviewedNative.WeakFourFirstOnly

open Polynomial Set
open RKCert.ReviewedNative.PolynomialBracket (ofCoeffs)
open RKCert.ReviewedNative.OrderedPolynomialSignStrips
open RKCert.ReviewedNative.PolynomialCertificate
open scoped BigOperators

universe u

def naturalVietaBand (high : Bool) (P T : List ℚ) {n : ℕ}
    (A : RationalStripFrame n) (den : ℕ) : RatBand :=
  let V := A.parameterBand den
  let S := A.nodeSum
  let f := projectiveValue high (listCoeff P 7) (listCoeff T 7) (listCoeff T 8)
  let p := f ![V.lo,S.lo]
  let q := f ![V.lo,S.hi]
  let r := f ![V.hi,S.lo]
  let s := f ![V.hi,S.hi]
  ⟨min (min p q) (min r s),max (max p q) (max r s)⟩

private theorem naturalVietaBand_ok (high : Bool) (P T : List ℚ) {n : ℕ}
    (A : RationalStripFrame n) (den : ℕ) :
    rawVietaOK high P T A den (naturalVietaBand high P T A den) := by
  let V := A.parameterBand den
  let S := A.nodeSum
  let f := projectiveValue high (listCoeff P 7) (listCoeff T 7) (listCoeff T 8)
  let p := f ![V.lo,S.lo]
  let q := f ![V.lo,S.hi]
  let r := f ![V.hi,S.lo]
  let s := f ![V.hi,S.hi]
  intro c
  have vertex_eq : vertex ![V.lo,S.lo] ![V.hi,S.hi] c =
      ![cond (c 0) V.hi V.lo,cond (c 1) S.hi S.lo] := by
    funext i
    fin_cases i <;> rfl
  change min (min p q) (min r s)≤f (vertex ![V.lo,S.lo] ![V.hi,S.hi] c) ∧
    f (vertex ![V.lo,S.lo] ![V.hi,S.hi] c)≤max (max p q) (max r s)
  rw [vertex_eq]
  cases h0 : c 0 <;> cases h1 : c 1 <;> simp only [h0,h1,Bool.cond_false,Bool.cond_true]
  · exact ⟨(min_le_left _ _).trans (min_le_left _ _),
      (le_max_left _ _).trans (le_max_left _ _)⟩
  · exact ⟨(min_le_left _ _).trans (min_le_right _ _),
      (le_max_right _ _).trans (le_max_left _ _)⟩
  · exact ⟨(min_le_right _ _).trans (min_le_left _ _),
      (le_max_left _ _).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (min_le_right _ _),
      (le_max_right _ _).trans (le_max_right _ _)⟩

def checkOrdinaryReceipts {n m : ℕ} (R : RationalFitCover (Fin n) n m)
    (P T : List ℚ) : Bool :=
  R.checkCages false P T (fun _ => true) &&
    R.claims.all (fun p => decide (∀ i,
      ordinaryCoordOK p.box i (p.source.band p.rank.1) (p.source.band (p.order i))))

def checkExteriorReceipts (R : RationalFitCover (Option (Fin 7)) 7 4)
    (P T : List ℚ) (high : Bool) : Bool :=
  (decide (listCoeff P 8=0 ∧ listCoeff P 7≠0 ∧ listCoeff T 8≠0) &&
    R.checkCages true P T (exteriorStopAllowed high)) &&
    R.claims.all (fun p => decide (∀ i, exteriorCoordOK (den:=R.den) high p
      (naturalVietaBand high P T p.source R.den) i))

noncomputable section
variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem RationalFitCover.den_pos_of_check {ι : Type*} [DecidableEq ι] [Fintype ι] {n m : ℕ}
    {R : RationalFitCover ι n m} {strict : Bool} {P T : List ℚ} {allowed : ι → Bool}
    (ok : R.checkCages strict P T allowed=true) : 0<R.den := by
  have h := ok
  simp only [RationalFitCover.checkCages,Bool.and_eq_true_iff] at h
  exact of_decide_eq_true h.1.1.1.1

theorem interiorCover_of_checked_rational_tables {n m : ℕ} {P T : List ℚ}
    (R : RationalFitCover (Fin n) n m) (ok : checkOrdinaryReceipts R P T=true) :
    InteriorCover ((ofCoeffs P).map (Rat.castHom K)) ((ofCoeffs T).map (Rat.castHom K)) n m := by
  obtain ⟨c,n⟩ := Bool.and_eq_true_iff.mp
    (show (R.checkCages false P T (fun _ => true) && _) = true from ok)
  apply interiorCover_of_rational_receipt R (RationalFitCover.den_pos_of_check c) c
  intro E p hp r cage pos
  have h : ∀ i, ordinaryCoordOK p.box i (p.source.band p.rank.1) (p.source.band (p.order i)) :=
    of_decide_eq_true (List.all_eq_true.mp n p hp)
  exact p.coordinates_of_ordinary_receipt h cage pos

theorem exteriorCover_of_checked_rational_tables {P T : List ℚ} {high : Bool}
    (R : RationalFitCover (Option (Fin 7)) 7 4) (ok : checkExteriorReceipts R P T high=true) :
    ExteriorCover ((ofCoeffs P).map (Rat.castHom K)) ((ofCoeffs T).map (Rat.castHom K)) high := by
  have h := ok
  simp only [checkExteriorReceipts,Bool.and_eq_true_iff] at h
  obtain ⟨⟨basis,c⟩,norm⟩ := h
  have coef : listCoeff P 8=0 ∧ listCoeff P 7≠0 ∧ listCoeff T 8≠0 := of_decide_eq_true basis
  apply exteriorCover_of_rational_receipt R (RationalFitCover.den_pos_of_check c) c
  intro E p hp v Hparam r e Hc actualSide F Vieta stop
  have nv : 0≤v := (show (0:K) ≤ gridCoord R.den p.source.span.1 from
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)).trans Hparam.1
  let W := naturalVietaBand high P T p.source R.den
  have boxes : ∀ i, exteriorCoordOK (den:=R.den) high p W i :=
    of_decide_eq_true (List.all_eq_true.mp norm p hp)
  exact p.coordinates_of_exterior_receipt W (naturalVietaBand_ok high P T p.source R.den)
    boxes coef.1 coef.2.1 coef.2.2 E nv Hparam Hc actualSide Vieta stop

/-- An accepted copy of each of the four chart families proves the exact
literal weak-four premise of the reviewed ordered ERK16 stage assembly. -/
theorem weakFourScalarExclusion_of_checked_rational_tables
    (cubic : RationalFitCover (Fin 7) 7 3)
    (interior : RationalFitCover (Fin 8) 8 4)
    (low high : RationalFitCover (Option (Fin 7)) 7 4)
    (A : checkOrdinaryReceipts cubic referenceJList referenceJList=true)
    (B : checkOrdinaryReceipts interior referenceP₀List referenceP₁List=true)
    (C : checkExteriorReceipts low referenceJList referenceP₀List false=true)
    (D : checkExteriorReceipts high referenceJList referenceN₁List true=true)
    {Q Z : K[X]} {a c : K}
    (H : RKResearch.Certified.ERK16.WeakFourChronologicalPorts Q Z a c) : False := by
  apply weakFourScalarExclusion_of_boxes firstPencilReferences_of_exact_moments ?_ H
  apply firstBoxCover_of_four_rational_covers
  · simpa only [referenceJList_polynomial,firstReferenceJ_map] using interiorCover_of_checked_rational_tables (K:=K) cubic A
  · simpa only [referenceP₀List_polynomial,referenceP₁List_polynomial,firstReferenceP₀_map,firstReferenceP₁_map] using
      interiorCover_of_checked_rational_tables (K:=K) interior B
  · simpa only [referenceJList_polynomial,referenceP₀List_polynomial,firstReferenceJ_map,firstReferenceP₀_map] using
      exteriorCover_of_checked_rational_tables (K:=K) low C
  · simpa only [referenceJList_polynomial,referenceN₁List_polynomial,firstReferenceJ_map,Polynomial.map_neg,firstReferenceP₁_map] using
      exteriorCover_of_checked_rational_tables (K:=K) high D

end
end RKCert.ReviewedNative.WeakFourFirstOnly
