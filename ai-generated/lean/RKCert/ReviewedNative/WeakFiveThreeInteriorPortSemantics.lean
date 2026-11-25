module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCoordinates
public import RKCert.ReviewedNative.WeakFiveThreeInteriorRatioBounds
public import RKCert.ReviewedNative.WeakFiveThreeInteriorBernsteinRows

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

@[expose] public section

/-! # Ordered-field transport and strict corner soundness

The chosen stops are strictly inside the ordered strip *by rank*, even
when an unrelated root cage starts at zero or ends at one. Every interval
inequality is closed. Strictness is used only for the denominators and
the final signed integers. -/
namespace RKCert.ReviewedNative.ThreeInteriorPencil

open RKCert.ReviewedNative.PolynomialCertificate
open RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

structure PortCellAdmissible (c : ThreeInteriorCell) : Prop where
  density : c.rect.xIndex < portDensityDen c
  strict : ∀ i, c.low i < c.high i
  top : ∀ i, c.high i ≤ 8192
  sep : ∀ ⦃i j⦄, i < j → c.high i < c.low j

theorem portCell_admissible_of_strip {rows : List ThreeInteriorCell}
    (H : ThreeInteriorFiniteStripRows rows) {c : ThreeInteriorCell} (hc : c ∈ rows) :
    PortCellAdmissible c :=
  ⟨H.densityIndex c hc,H.strict c hc,H.top c hc,H.separated c hc⟩

private theorem leftStop_not_first (w : ThreeInteriorWord) (hs : w.port.side = false) :
    (0:Fin 7) < wordSiteRank w (.inr (portStop w.port)) := by
  cases w <;> first | decide | cases hs

private theorem rightStop_not_last (w : ThreeInteriorWord) (hs : w.port.side = true) :
    wordSiteRank w (.inr (portStop w.port)) < (6:Fin 7) := by
  cases w <;> first | decide | cases hs

private theorem leftStopIndex_pos {c : ThreeInteriorCell} (H : PortCellAdmissible c)
    (w : ThreeInteriorWord) (hs : w.port.side = false) (b : Bool) :
    0 < portCageIndex c w b (.inr (portStop w.port)) := by
  have lp : 0 < c.low (wordSiteRank w (.inr (portStop w.port))) :=
    (Nat.zero_le _).trans_lt ((H.strict 0).trans (H.sep (leftStop_not_first w hs)))
  cases b
  · exact lp
  · exact lp.trans (H.strict _)

private theorem rightStopIndex_lt_top {c : ThreeInteriorCell} (H : PortCellAdmissible c)
    (w : ThreeInteriorWord) (hs : w.port.side = true) (b : Bool) :
    portCageIndex c w b (.inr (portStop w.port)) < 8192 := by
  have hi : c.high (wordSiteRank w (.inr (portStop w.port))) < 8192 :=
    (H.sep (rightStop_not_last w hs)).trans_le ((H.strict 6).le.trans (H.top 6))
  cases b
  · exact (H.strict _).trans hi
  · exact hi

private theorem densityIndex_le_den {c : ThreeInteriorCell} (H : PortCellAdmissible c)
    (b : Bool) : portDensityIndex c b ≤ portDensityDen c := by
  cases b
  · exact H.density.le
  · exact H.density

private theorem portDensityDen_pos (c : ThreeInteriorCell) : 0 < portDensityDen c := by
  unfold portDensityDen
  positivity

private theorem gammaDen_left {S i d : ℤ} (S0 : 0 < S) (i0 : 0 ≤ i) (iS : i ≤ S)
    (d0 : 0 < d) : 0 < i*8192+(S-i)*d := by
  by_cases hz : i = 0
  · simpa only [hz,zero_mul,sub_zero,zero_add] using mul_pos S0 d0
  · have h0i : (0 : ℤ) ≠ i := fun e => hz e.symm
    exact add_pos_of_pos_of_nonneg (mul_pos (lt_of_le_of_ne i0 h0i) (by decide))
      (mul_nonneg (sub_nonneg.mpr iS) d0.le)

private theorem wordRootEnd_den_pos {c : ThreeInteriorCell} (H : PortCellAdmissible c)
    (w : ThreeInteriorWord) (i : Fin w.port.count) (b : Bool) :
    0 < (wordRootEnd c w i b).den := by
  cases hs : w.port.side
  · have z := leftStopIndex_pos H w hs (!b)
    have zi : (0:ℤ) < (portCageIndex c w (!b) (.inr (portStop w.port)) : ℤ) := by exact_mod_cast z
    simpa only [wordRootEnd,homogeneousRoot,hs,Bool.false_eq_true,if_false] using zi
  · have z := rightStopIndex_lt_top H w hs (!b)
    have zi : (portCageIndex c w (!b) (.inr (portStop w.port)) : ℤ) < 8192 := by exact_mod_cast z
    simpa only [wordRootEnd,homogeneousRoot,hs,if_true] using sub_pos.mpr zi

private theorem wordGammaEnd_den_pos {c : ThreeInteriorCell} (H : PortCellAdmissible c)
    (w : ThreeInteriorWord) (b : Bool) : 0 < (wordGammaEnd c w b).den := by
  have Sc : (0:ℤ) < (portDensityDen c:ℤ) := by exact_mod_cast portDensityDen_pos c
  cases hs : w.port.side
  · have z := leftStopIndex_pos H w hs b
    have i0 : (0:ℤ) ≤ (portDensityIndex c (!b):ℤ) := by positivity
    have iS : (portDensityIndex c (!b):ℤ) ≤ (portDensityDen c:ℤ) := by
      exact_mod_cast densityIndex_le_den H (!b)
    have d0 : (0:ℤ) < (portCageIndex c w b (.inr (portStop w.port)):ℤ) := by exact_mod_cast z
    simpa only [wordGammaEnd,homogeneousGamma,hs,Bool.false_eq_true,if_false,Bool.cond_false]
      using gammaDen_left Sc i0 iS d0
  · simpa only [wordGammaEnd,homogeneousGamma,hs,if_true]
      using (mul_pos Sc (by decide : (0:ℤ) < 8192))

private theorem wordCount_le_four (w : ThreeInteriorWord) : w.port.count ≤ 4 := by
  cases w <;> decide

private theorem wordExponent_one_two (w : ThreeInteriorWord) :
    w.port.exponent = 1 ∨ w.port.exponent = 2 := by
  cases w <;> decide

private theorem word_vertex (c : ThreeInteriorCell) (w : ThreeInteriorWord)
    (a : Fin (w.port.count+1) → Bool) :
    vertex (wordPortBounds c w false) (wordPortBounds c w true) a =
      Fin.cons ((wordGammaEnd c w (a 0)).value (K := ℚ))
        (fun j => (wordRootEnd c w j (a j.succ)).value) := by
  funext i
  cases i using Fin.cases with
  | zero => cases h : a 0 <;> simp only [vertex,wordPortBounds,h,Bool.cond_false,Bool.cond_true,Fin.cons_zero]
  | succ j => cases h : a j.succ <;> simp only [vertex,wordPortBounds,h,Bool.cond_false,Bool.cond_true,Fin.cons_succ]

/-- The exact all-corner field inequality follows from a small integer
check at the same cell and word. -/
theorem checkPortWord_sound {c : ThreeInteriorCell} (H : PortCellAdmissible c)
    {w : ThreeInteriorWord} (check : checkPortWord c w = true)
    (a : Fin (w.port.count+1) → Bool) :
    threeInteriorSigned w.positive
      (threeInteriorLocalizer w.port (vertex (wordPortBounds c w false) (wordPortBounds c w true) a)) := by
  rw [word_vertex]
  exact portRootCorners_sound (wordExponent_one_two w) (wordCount_le_four w)
    (wordRootEnd c w) (wordGammaEnd c w) (wordRootEnd_den_pos H w)
    (wordGammaEnd_den_pos H w) check (fun j => a j.succ) (a 0)

section OrderedField
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem densityEnd_nonneg (c : ThreeInteriorCell) (b : Bool) :
    0 ≤ portDensityEnd (K := K) c b :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

private theorem densityEnd_le_one {c : ThreeInteriorCell} (H : PortCellAdmissible c) (b : Bool) :
    portDensityEnd (K := K) c b ≤ 1 := by
  have pos : 0 < (portDensityDen c:K) := Nat.cast_pos.mpr (portDensityDen_pos c)
  apply (div_le_one pos).2
  exact Nat.cast_le.mpr (densityIndex_le_den H b)

private theorem cageEnd_nonneg (c : ThreeInteriorCell) (w : ThreeInteriorWord) (b : Bool)
    (a : ThreeInteriorSite) : 0 ≤ portCageEnd (K := K) c w b a :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

private theorem cageEnd_upper_le_one {c : ThreeInteriorCell} (H : PortCellAdmissible c)
    (w : ThreeInteriorWord) (a : ThreeInteriorSite) : portCageEnd (K := K) c w true a ≤ 1 := by
  have pos : 0 < ((8192:ℕ):K) := Nat.cast_pos.mpr (by decide)
  apply (div_le_one pos).2
  exact Nat.cast_le.mpr (H.top (wordSiteRank w a))

private theorem leftStop_end_pos {c : ThreeInteriorCell} (H : PortCellAdmissible c)
    (w : ThreeInteriorWord) (hs : w.port.side = false) :
    0 < portCageEnd (K := K) c w false (.inr (portStop w.port)) :=
  div_pos (Nat.cast_pos.mpr (leftStopIndex_pos H w hs false)) (Nat.cast_pos.mpr (by decide))

private theorem rightStop_end_lt_one {c : ThreeInteriorCell} (H : PortCellAdmissible c)
    (w : ThreeInteriorWord) (hs : w.port.side = true) :
    portCageEnd (K := K) c w true (.inr (portStop w.port)) < 1 := by
  have pos : 0 < ((8192:ℕ):K) := Nat.cast_pos.mpr (by decide)
  apply (div_lt_one pos).2
  exact Nat.cast_lt.mpr (rightStopIndex_lt_top H w hs true)

/-- Reconstruct the actual tuple from its seven word-ordered root cages.
The formulas work in every ordered field, on the closed s/j rectangle,
including the unit seams at any other site. -/
theorem actualPortArgs_mem {c : ThreeInteriorCell} (H : PortCellAdmissible c)
    {w : ThreeInteriorWord} {s j : K} {r : Fin 3 → K} {m : Fin 4 → K}
    (cell : InDyadicRect c.rect s j) (cages : c.contains (w.sites r m)) :
    ∀ i, threeInteriorLocalizerArgs w.port s r m i ∈
      Set.Icc (wordPortBounds c w false i:K) (wordPortBounds c w true i:K) := by
  have sb : s ∈ Set.Icc (portDensityEnd c false) (portDensityEnd c true) := cell.1
  have db : m (portStop w.port) ∈
      Set.Icc (portCageEnd c w false (.inr (portStop w.port)))
        (portCageEnd c w true (.inr (portStop w.port))) :=
    portCage_actual cages (.inr (portStop w.port))
  have s0 : 0 ≤ portDensityEnd (K := K) c false := densityEnd_nonneg c false
  have s1 : portDensityEnd (K := K) c true ≤ 1 := densityEnd_le_one H true
  rw [actualLocalizerArgs_cons]
  intro i
  cases i using Fin.cases with
  | zero =>
      simp only [Fin.cons_zero, wordPortBounds]
      rw [portFraction_value_cast (K := K) (wordGammaEnd c w false),
        portFraction_value_cast (K := K) (wordGammaEnd c w true)]
      rw [wordGammaEnd_value (K := K) c w false, wordGammaEnd_value (K := K) c w true]
      cases hs : w.port.side
      · simpa only [hs,Bool.false_eq_true,if_false,Bool.not_false,Bool.not_true] using
          threeInterior_leftGamma_bounds s0 s1 (leftStop_end_pos H w hs) sb db
      · have d1 := (rightStop_end_lt_one (K := K) H w hs).le
        simpa only [hs,if_true,Bool.not_false,Bool.not_true] using
          threeInterior_rightGamma_bounds s1 d1 sb db
  | succ i =>
      simp only [Fin.cons_succ, wordPortBounds]
      rw [portFraction_value_cast (K := K) (wordRootEnd c w i false),
        portFraction_value_cast (K := K) (wordRootEnd c w i true)]
      rw [wordRootEnd_value (K := K) c w i false, wordRootEnd_value (K := K) c w i true]
      have xb := portCage_actual cages (portFactorSite w.port i)
      cases hs : w.port.side
      · have x0 : 0 ≤ portCageEnd (K := K) c w false (portFactorSite w.port i) :=
          cageEnd_nonneg _ _ _ _
        simpa only [hs,Bool.false_eq_true,if_false,Bool.not_false,Bool.not_true] using
          threeInterior_leftRoot_bounds x0 (leftStop_end_pos H w hs) xb db
      · have x1 : portCageEnd (K := K) c w true (portFactorSite w.port i) ≤ 1 :=
          cageEnd_upper_le_one H w _
        simpa only [hs,if_true,Bool.not_false,Bool.not_true] using
          threeInterior_rightRoot_bounds x1 (rightStop_end_lt_one H w hs) xb db

end OrderedField

end RKCert.ReviewedNative.ThreeInteriorPencil
