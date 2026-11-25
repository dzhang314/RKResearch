module

public import RKCert.ReviewedNative.ERKOrder16WeakFourRankFour
public import RKCert.ReviewedNative.ERKOrder16WeakFourSimpleOrigin
public import RKCert.ReviewedNative.ERKOrder16WeakFourInactiveAlias
public import RKCert.ReviewedNative.ERKOrder16WeakFourRepeatedOrigin
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace RKResearch.Certified.ERK16

open Polynomial Module RKCert.Endpoint RKCert.Endpoint.WeightedClock RKCert.OneEscape
open RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse
open RKResearch.Certified.Graded.Reverse.Thin
open scoped Classical BigOperators Matrix

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A : Matrix (Fin 24) (Fin 24) K} {b w : Fin 24 → K}
variable {U : Submodule K (Fin 24 → K)} {Q P : K[X]}

/-- The exact physical possibilities left in the four-numerical-site
branch after the rank-four, simple active-origin, and inactive shared-clock cuts.
Five physical rows are allowed only with the original origin active. -/
structure Width24WeakFourRemaining (A : Matrix (Fin 24) (Fin 24) K)
    (b : Fin 24 → K) (Q P : K[X]) : Prop where
  carrierThree : finrank K (width24WeakFiveCarrier A b) = 3
  fourSites : (weightedSites (reflectedClock A) (reverseContrast A b Q P)).card = 4
  seedRows : (Hidden.activeRows (quadraticSeed A b)).card = 15
  originClock : reflectedClock A 0 = 1
  originSeedZero : quadraticSeed A b 0 = 0
  fitAtOneNonzero : Q.eval 1 ≠ 0
  physical :
    ((weakFiveRows A b Q P).card = 5 ∧ (0 : Fin 24) ∈ weakFiveRows A b Q P) ∨
    ((weakFiveRows A b Q P).card = 4 ∧
      Set.InjOn (reflectedClock A) (weakFiveRows A b Q P : Set (Fin 24)) ∧
      (0 : Fin 24) ∉ weakFiveRows A b Q P ∧ b 0 = 0 ∧
      ∀ i ∈ weakFiveRows A b Q P, reflectedClock A i ≠ 1)

/-- Refine the actual ordinary four-site chart. The initial support
budget derives the exhaustive carrier-rank selector; the second pays
the original origin once, even when it is not in contrast support. -/
theorem Width24OrdinaryWeakHead.weak_four_remaining_physical_cases
    (L : Width24OrdinaryWeakHead A b U w Q P)
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : RKResearch.HasOrder 16 A b)
    (seven : finrank K (zeroSpace A 7) = 7)
    (four : (weightedSites (reflectedClock A) (reverseContrast A b Q P)).card = 4) :
    Width24WeakFourRemaining A b Q P := by
  classical
  let c := nodes A
  let y := reflectedClock A
  let d := quadraticSeed A b
  let t : Fin 24 := Fin.last 23
  let v := reverseContrast A b Q P
  let V := weakFiveRows A b Q P
  let cover := width24_quadratic_cover ha ho
  have n0t : (0 : Fin 24) ≠ t := by
    change (0 : Fin 24) ≠ Fin.last 23
    decide
  have c0 : c 0 = 0 := by
    change (∑ j, A 0 j * (1 : K)) = 0
    exact Finset.sum_eq_zero fun j _ => by rw [ha 0 j (Fin.zero_le j), zero_mul]
  have y0 : y 0 = 1 := by
    change 1 - c 0 = 1
    rw [c0, sub_zero]
  have yt : y t = 0 := by
    change 1 - nodes A (Fin.last 23) = 0
    rw [cover.frame.lastClock, sub_self]
  have data (i : Fin 24) (hv : v i ≠ 0) :
      d i = 0 ∧ y i ≠ 0 ∧ b i ≠ 0 :=
    let h := reverse_contrast_true_support L.qFit L.pFit i hv
    ⟨h.1, h.2.1, h.2.2.1⟩
  have vt : v t = 0 := by
    by_contra h
    exact (data t h).2.1 yt
  have seedOff (i : Fin 24) (hi : d i ≠ 0) : v i = 0 := by
    by_contra h
    exact hi (data i h).1
  have blindOff (i : Fin 24) (hi : i ∈ Hidden.blindRows c b d 0 t) : v i = 0 := by
    by_contra h
    exact (mul_ne_zero (data i h).2.1 (data i h).2.2)
      ((Hidden.mem_blindRows i).mp hi).2.2.2
  have budget := Hidden.carrier_contrast_budget (c := c) (o := (0 : Fin 24))
    cover.frame.lastLive.live cover.lastSeed vt seedOff blindOff
  change finrank K (width24WeakFiveCarrier A b) + (Hidden.activeRows d).card +
    V.card + 1 ≤ 24 at budget
  have seedLower : 15 ≤ (Hidden.activeRows d).card := width24_seed_rows_ge_fifteen ha ho
  have image : V.image y = weightedSites (reflectedClock A) (reverseContrast A b Q P) := by
    ext x
    simp only [Finset.mem_image, mem_weightedSites, V, y, mem_weakFiveRows]
  have vLower : 4 ≤ V.card := by
    have h := Finset.card_image_le (s := V) (f := y)
    rwa [image, four] at h
  have u3 : finrank K U = 3 := by
    have base := L.flat.baseRank
    have h := L.flat.ranks 2 (by decide)
    change finrank K (zeroSpace A 7) = finrank K (zeroSpace A 5) + 2 at h
    omega
  have hLower : 3 ≤ finrank K (width24WeakFiveCarrier A b) := by
    rw [← u3]
    exact Submodule.finrank_mono L.coreInside
  have rankCases : finrank K (width24WeakFiveCarrier A b) = 3 ∨
      finrank K (width24WeakFiveCarrier A b) = 4 := by omega
  have h3 : finrank K (width24WeakFiveCarrier A b) = 3 := by
    rcases rankCases with h | h
    · exact h
    · exact (L.weak_four_carrier_four_impossible ha ho seven h four).elim
  have Q1 := L.reflected_origin_live_of_carrier_three ha ho h3
  have w5 : w ∈ zeroSpace A 5 := by
    have flag : zeroSpace A 5 = chain (diag c) U w 2 := L.flat.flags 0 (by decide)
    rw [flag]
    have h := ((clock_chain_le_iff (T := diag c) (U := U) (w := w) 2).mp le_rfl).2
      0 (by decide)
    simpa only [pow_zero, Module.End.one_eq_id, LinearMap.id_apply] using h
  have w0 : w 0 = 0 := origin_zeroSpace ha 5 w5
  have d0 : d 0 = 0 := by
    have h := L.qFit 0
    change d 0 * w 0 = Q.eval (y 0) * d 0 at h
    rw [w0, y0, mul_zero] at h
    exact (mul_eq_zero.mp h.symm).resolve_left Q1
  have result : (Hidden.activeRows d).card = 15 ∧
      ((V.card = 5 ∧ (0 : Fin 24) ∈ V) ∨
        (V.card = 4 ∧ Set.InjOn y (V : Set (Fin 24)) ∧ (0 : Fin 24) ∉ V ∧
          b 0 = 0 ∧ ∀ i ∈ V, y i ≠ 1)) := by
    by_cases active : (0 : Fin 24) ∈ V
    · have v5 : V.card = 5 := by
        by_contra different
        have v4 : V.card = 4 := by omega
        exact L.weak_four_simple_active_origin_impossible ha ho h3 four v4 active
      exact ⟨by omega, Or.inl ⟨v5, active⟩⟩
    · -- This auxiliary column is used for a support count only.
      -- Neither the tableau nor its weights are altered.
      let aux : Fin 24 → K := fun i => if i = 0 then 1 else v i
      have auxT : aux t = 0 := by simp [aux, n0t.symm, vt]
      have auxSeed (i : Fin 24) (hi : d i ≠ 0) : aux i = 0 := by
        have ni : i ≠ 0 := fun eq => hi (eq.symm ▸ d0)
        simp [aux, ni, seedOff i hi]
      have auxBlind (i : Fin 24) (hi : i ∈ Hidden.blindRows c b d 0 t) : aux i = 0 := by
        simp [aux, ((Hidden.mem_blindRows i).mp hi).1, blindOff i hi]
      have support : Hidden.activeRows aux = insert 0 V := by
        ext i
        by_cases eq : i = 0
        · subst i
          simp [aux]
        · simp [aux, eq, V, v]
      have paid := Hidden.carrier_contrast_budget (c := c) (o := (0 : Fin 24))
        cover.frame.lastLive.live cover.lastSeed auxT auxSeed auxBlind
      change finrank K (width24WeakFiveCarrier A b) + (Hidden.activeRows d).card +
        (Hidden.activeRows aux).card + 1 ≤ 24 at paid
      rw [support, Finset.card_insert_of_notMem active] at paid
      have v4 : V.card = 4 := by omega
      have simple : Set.InjOn y (V : Set (Fin 24)) := by
        apply Finset.card_image_iff.mp
        rw [image, four, v4]
      have noAlias (i : Fin 24) (hi : i ∈ V) : y i ≠ 1 := by
        intro eq
        exact L.weak_four_inactive_origin_shared_clock_impossible ha ho h3 four v4 active
          ⟨i, hi, eq⟩
      have b0 : b 0 = 0 := by
        have h : reverseContrast A b Q P 0 = 0 := by
          by_contra hv
          exact active ((mem_weakFiveRows 0).mpr hv)
        simp only [reverseContrast, Pi.sub_apply, weightedEval_apply, eval_mul, eval_X,
          show reflectedClock A 0 = 1 from y0, show quadraticSeed A b 0 = 0 from d0,
          one_mul, mul_zero, sub_zero] at h
        exact (mul_eq_zero.mp h).resolve_left Q1
      exact ⟨by omega, Or.inr ⟨v4, simple, active, b0, noAlias⟩⟩
  exact ⟨h3, four, result.1, y0, d0, Q1, result.2⟩

/-- In the ordinary four-site case, all four rows have distinct clocks.
The original origin has zero weight and does not share a contrast clock. -/
theorem Width24OrdinaryWeakHead.weak_four_inactive_unshared_remaining
    (L : Width24OrdinaryWeakHead A b U w Q P)
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : RKResearch.HasOrder 16 A b)
    (seven : finrank K (zeroSpace A 7) = 7)
    (four : (weightedSites (reflectedClock A) (reverseContrast A b Q P)).card = 4) :
    (weakFiveRows A b Q P).card = 4 ∧
      Set.InjOn (reflectedClock A) (weakFiveRows A b Q P : Set (Fin 24)) ∧
      (0 : Fin 24) ∉ weakFiveRows A b Q P ∧ b 0 = 0 ∧
      ∀ i ∈ weakFiveRows A b Q P, reflectedClock A i ≠ 1 := by
  have packet := L.weak_four_remaining_physical_cases ha ho seven four
  rcases packet.physical with ⟨five, origin⟩ | remaining
  · exact False.elim
      (L.weak_four_repeated_active_origin_impossible ha ho packet.carrierThree four five origin)
  · exact remaining

end
end RKResearch.Certified.ERK16
