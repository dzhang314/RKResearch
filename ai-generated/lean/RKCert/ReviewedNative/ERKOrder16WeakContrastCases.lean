module

public import RKCert.ReviewedNative.ReverseContrastSiteBudget
public import RKCert.ReviewedNative.ERKOrder16WeakHead

@[expose] public section

/-! # The ordinary native weak rank-seven contrast dispatch

The lower bound comes from the paid X-weighted moments. The upper
bound counts physical seed and contrast rows, a compensated carrier
of dimension at least three, and the independent live terminal. -/
namespace RKResearch.Certified.ERK16

open RKResearch Module Polynomial
open RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse
open RKResearch.Certified.Graded.Reverse.Thin
open RKCert.Endpoint.WeightedClock

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A : Matrix (Fin 24) (Fin 24) K} {b : Fin 24 → K}

/-- Four or five distinct numerical contrast clocks for the same
actual head. In the four-site case this does not claim four rows. -/
theorem width24_ordinary_weak_contrast_four_or_five
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 16 A b)
    (seven : finrank K (zeroSpace A 7) = 7)
    {U : Submodule K (Fin 24 → K)} {w : Fin 24 → K} {Q P : K[X]}
    (L : Width24OrdinaryWeakHead A b U w Q P) :
    (weightedSites (reflectedClock A) (reverseContrast A b Q P)).card = 4 ∨
      (weightedSites (reflectedClock A) (reverseContrast A b Q P)).card = 5 := by
  classical
  let y := reflectedClock A
  let d := quadraticSeed A b
  let t := Fin.last 23
  let W := reverseContrast A b Q P
  let S := weightedSites y W
  change S.card = 4 ∨ S.card = 5
  have qd := L.qDegree
  have pd := L.pDegree
  have low : 3 < S.card :=
    reverse_contrast_sites_gt_of_paid_moments ho (r := 3) (P := P)
      L.qNonzero (by omega) (by omega)
  have uRank : finrank K U = 3 := by
    have flag := L.flat.ranks 2 le_rfl
    change finrank K (zeroSpace A 7) = finrank K (zeroSpace A 5) + 2 at flag
    have base := L.flat.baseRank
    omega
  have carrierRank : 3 ≤ finrank K (width24WeakFiveCarrier A b) := by
    rw [← uRank]
    exact Submodule.finrank_mono L.coreInside
  have seedRows : 15 ≤ (Hidden.activeRows d).card :=
    width24_seed_rows_ge_fifteen ha ho
  let C := width24_quadratic_cover ha ho
  have y0 : y t = 0 := by
    change 1 - nodes A (Fin.last 23) = 0
    rw [C.frame.lastClock, sub_self]
  have terminalZero : W t = 0 := by
    by_contra active
    exact (reverse_contrast_true_support L.qFit L.pFit t active).2.1 y0
  have seedZero (i : Fin 24) (hi : d i ≠ 0) : W i = 0 := by
    by_contra active
    exact hi (reverse_contrast_true_support L.qFit L.pFit i active).1
  have blindZero (i : Fin 24) (hi : i ∈ Hidden.blindRows (nodes A) b d 0 t) :
      W i = 0 := by
    by_contra active
    obtain ⟨_, yn, bn, _, _⟩ := reverse_contrast_true_support L.qFit L.pFit i active
    exact mul_ne_zero yn bn ((Hidden.mem_blindRows i).mp hi).2.2.2
  have paid := Hidden.carrier_contrast_budget (c := nodes A) (o := 0)
    C.frame.lastLive.live C.lastSeed terminalZero seedZero blindZero
  change finrank K (width24WeakFiveCarrier A b) + (Hidden.activeRows d).card +
    (Hidden.activeRows W).card + 1 ≤ 24 at paid
  have image : (Hidden.activeRows W).image y = S := by
    ext a
    simp only [S, Finset.mem_image, Hidden.mem_activeRows, mem_weightedSites]
  have sitesToRows : S.card ≤ (Hidden.activeRows W).card := by
    rw [← image]
    exact Finset.card_image_le
  omega

/-- The rank-seven dispatcher supplies the true head and chooses its
four- or five-site case without any input contrast count. -/
theorem width24_ordinary_weak_contrast_cases
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 16 A b)
    (seven : finrank K (zeroSpace A 7) = 7) :
    ∃ (U : Submodule K (Fin 24 → K)) (w : Fin 24 → K) (Q P : K[X]),
      Width24OrdinaryWeakHead A b U w Q P ∧
        ((weightedSites (reflectedClock A) (reverseContrast A b Q P)).card = 4 ∨
          (weightedSites (reflectedClock A) (reverseContrast A b Q P)).card = 5) := by
  obtain ⟨U, w, Q, P, L⟩ := width24_ordinary_weak_head ha ho seven
  exact ⟨U, w, Q, P, L, width24_ordinary_weak_contrast_four_or_five ha ho seven L⟩

end
end RKResearch.Certified.ERK16
