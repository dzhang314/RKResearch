module

public import RKCert.ReviewedNative.ERKOrder16WeakFourFivePlusOne

@[expose] public section

namespace RKResearch.Certified.ERK16

open Polynomial RKCert.Endpoint.WeightedClock
open RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse
open RKResearch.Certified.Graded.Reverse.Thin
open scoped Classical BigOperators Matrix

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A : Matrix (Fin 24) (Fin 24) K} {b w : Fin 24 → K}
variable {U : Submodule K (Fin 24 → K)} {Q P : K[X]}

/-- The actual rank-three weak mask on the five contrast rows and the
live terminal. Four nonzero contrast clocks give one repeated group
among these six rows. Its diagonal is not inferred from the combined
mass of that group. -/
theorem Width24OrdinaryWeakHead.weak_four_repeated_active_origin_impossible
    (L : Width24OrdinaryWeakHead A b U w Q P)
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : RKResearch.HasOrder 16 A b)
    (rankThree : Module.finrank K (width24WeakFiveCarrier A b) = 3)
    (four : (weightedSites (reflectedClock A) (reverseContrast A b Q P)).card = 4)
    (physical : (weakFiveRows A b Q P).card = 5)
    (origin : (0 : Fin 24) ∈ weakFiveRows A b Q P) : False := by
  classical
  obtain ⟨q, θ, W, src⟩ := L.rank_three_forward_mask_with_source ha ho rankThree
  let y := reflectedClock A
  let V := weakFiveRows A b Q P
  let t : Fin 24 := Fin.last 23
  let S := insert t V
  let cover := width24_quadratic_cover ha ho
  have data (i : Fin 24) (hi : i ∈ V) : quadraticSeed A b i = 0 ∧ y i ≠ 0 := by
    have h := reverse_contrast_true_support L.qFit L.pFit i ((mem_weakFiveRows i).mp hi)
    exact ⟨h.1, h.2.1⟩
  have yt : y t = 0 := by
    change 1 - nodes A (Fin.last 23) = 0
    rw [cover.frame.lastClock, sub_self]
  have y0 : y 0 = 1 := by
    have h : nodes A (0 : Fin 24) = 0 := by
      change (∑ k, A 0 k * (1 : K)) = 0
      exact Finset.sum_eq_zero fun k _ => by rw [ha 0 k (Fin.zero_le k), zero_mul]
    change 1 - nodes A 0 = 1
    rw [h, sub_zero]
  have nt : t ∉ V := fun h => (data t h).2 yt
  have size : S.card = 6 := by
    change (insert t V).card = 6
    rw [Finset.card_insert_of_notMem nt, show V.card = 5 from physical]
  have imageV : V.image y = weightedSites (reflectedClock A) (reverseContrast A b Q P) := by
    ext x
    simp only [Finset.mem_image, mem_weightedSites, V, y, mem_weakFiveRows]
  have terminalNew : y t ∉ V.image y := by
    intro h
    obtain ⟨i, hi, e⟩ := Finset.mem_image.mp h
    exact (data i hi).2 (e.trans yt)
  have siteCount : (S.image y).card = 5 := by
    change ((insert t V).image y).card = 5
    rw [Finset.image_insert, Finset.card_insert_of_notMem terminalNew, imageV, four]
  have fewer : (S.image y).card < S.card := by
    rw [siteCount, size] <;> decide
  obtain ⟨j, jS, i, iS, ji, sameClock⟩ := Finset.exists_ne_map_eq_of_card_image_lt fewer
  let C := S.erase j
  have jOut : j ∉ C := Finset.notMem_erase j S
  have iIn : i ∈ C := Finset.mem_erase.mpr ⟨ji.symm, iS⟩
  have whole : insert j C = S := Finset.insert_erase jS
  have five : C.card = 5 := by
    change (S.erase j).card = 5
    rw [Finset.card_erase_of_mem jS, size]
  have repeatMem : y j ∈ C.image y := Finset.mem_image.mpr ⟨i, iIn, sameClock.symm⟩
  have sameImage : C.image y = S.image y := calc
    _ = insert (y j) (C.image y) := (Finset.insert_eq_of_mem repeatMem).symm
    _ = (insert j C).image y := (Finset.image_insert y j C).symm
    _ = _ := congrArg (fun T : Finset (Fin 24) => T.image y) whole
  have simple : Set.InjOn y (C : Set (Fin 24)) :=
    Finset.card_image_iff.mp (by rw [sameImage, siteCount, five])
  have endpoint (r : K) (k : Fin 24) (hk : k ∈ S) (eq : y k = r) : ∃ l ∈ C, y l = r := by
    have e : r ∈ C.image y := by
      rw [sameImage]
      exact Finset.mem_image.mpr ⟨k, hk, eq⟩
    exact Finset.mem_image.mp e
  have mask : WeakFourGradedMask A b θ q Q S := by
    refine ⟨W.degree, W.reflected, src, ?_, ?_⟩
    · intro k hk
      have hV : k ∉ V := fun e => hk (Finset.mem_insert_of_mem e)
      have h0 : k ≠ 0 := fun e => hV (e.symm ▸ origin)
      have ht : k ≠ t := fun e => hk (e.symm ▸ Finset.mem_insert_self t V)
      exact W.outside k hV h0 ht
    · intro k hk
      rcases Finset.mem_insert.mp hk with h | h
      · rw [h]
        exact cover.lastSeed
      · exact (data k h).1
  rw [← whole] at mask
  exact mask.five_plus_one_impossible ha ho L.qNonzero L.qDegree five jOut simple
    (endpoint 0 t (Finset.mem_insert_self t V) yt)
    (endpoint 1 0 (Finset.mem_insert_of_mem origin) y0)
    (Or.inl ⟨i, iIn, sameClock.symm⟩)

end
end RKResearch.Certified.ERK16
