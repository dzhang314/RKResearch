module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.List.Basic
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.Monotone.Basic

import Mathlib.Tactic.NormNum

@[expose] public section

/-! # Exact finite slicing certificates for dyadic covers

No field points are enumerated by the checker. Its input is a chain of
horizontal slices and, on each slice, an accepted vertical chain of
rectangles from the original list. Soundness is over every ordered field
and includes all of the closed slice boundaries. -/

namespace RKCert.ReviewedNative.PolynomialCertificate

/-- A contiguous chain of closed spans from start to finish. The current
span may be degenerate; an empty chain only passes when start equals finish. -/
def checkChain (finish : ℕ) : ℕ → List (ℕ × ℕ) → Bool
  | start, [] => decide (start = finish)
  | start, (a, b) :: tail =>
      decide (start = a ∧ a ≤ b) && checkChain finish b tail

/-- An accepted finite chain covers the whole closed interval in any
linear order with a strictly increasing interpretation of the grid. -/
theorem checkChain_covers {α : Type*} [LinearOrder α]
    (interpret : ℕ → α) (mono : StrictMono interpret)
    (spans : List (ℕ × ℕ)) {start finish : ℕ}
    (nondegenerate : start < finish) (accepted : checkChain finish start spans = true)
    {x : α} (hx : x ∈ Set.Icc (interpret start) (interpret finish)) :
    ∃ ab ∈ spans, x ∈ Set.Icc (interpret ab.1) (interpret ab.2) := by
  induction spans generalizing start with
  | nil =>
      have e : start = finish := by simpa [checkChain] using accepted
      exact False.elim (nondegenerate.ne e)
  | cons head spans ih =>
      rcases head with ⟨a, b⟩
      have h := Bool.and_eq_true_iff.mp
        (show (decide (start = a ∧ a ≤ b) && checkChain finish b spans) = true from accepted)
      have ha : start = a := (of_decide_eq_true h.1).1
      by_cases hxb : x ≤ interpret b
      · exact ⟨(a, b), List.mem_cons.mpr (Or.inl rfl),
          ⟨by simpa only [ha] using hx.1, hxb⟩⟩
      · have hbx := lt_of_not_ge hxb
        have hbf : b < finish := mono.lt_iff_lt.mp (hbx.trans_le hx.2)
        obtain ⟨ab, hab, hmem⟩ := ih hbf h.2 ⟨hbx.le, hx.2⟩
        exact ⟨ab, List.mem_cons.mpr (Or.inr hab), hmem⟩

/-- A rectangle whose coordinates use a common integer grid on each axis. -/
structure GridRect where
  xLo : ℕ
  xHi : ℕ
  yLo : ℕ
  yHi : ℕ
  deriving DecidableEq, Repr

/-- A slice contains a list of actual rectangles spanning the full slice. -/
structure GridSlice where
  xLo : ℕ
  xHi : ℕ
  vertical : List GridRect
  deriving Repr

def checkSlice (rows : List GridRect) (height : ℕ) (slice : GridSlice) : Bool :=
  (slice.vertical.all fun c => decide (c ∈ rows ∧ c.xLo ≤ slice.xLo ∧ slice.xHi ≤ c.xHi)) &&
    checkChain height 0 (slice.vertical.map fun c => (c.yLo, c.yHi))

def checkGridCover (rows : List GridRect) (width height : ℕ) (slices : List GridSlice) : Bool :=
  checkChain width 0 (slices.map fun sl => (sl.xLo, sl.xHi)) &&
    slices.all (checkSlice rows height)

/-- Both axes can be interpreted by arbitrary strictly increasing grids.
The returned rectangle is one of the rows, not an auxiliary slice cell. -/
theorem checkGridCover_covers {α β : Type*} [LinearOrder α] [LinearOrder β]
    (X : ℕ → α) (Y : ℕ → β) (monoX : StrictMono X) (monoY : StrictMono Y)
    {rows : List GridRect} {width height : ℕ} {slices : List GridSlice}
    (wpos : 0 < width) (hpos : 0 < height)
    (accepted : checkGridCover rows width height slices = true)
    {x : α} {y : β} (hx : x ∈ Set.Icc (X 0) (X width))
    (hy : y ∈ Set.Icc (Y 0) (Y height)) :
    ∃ c ∈ rows, x ∈ Set.Icc (X c.xLo) (X c.xHi) ∧ y ∈ Set.Icc (Y c.yLo) (Y c.yHi) := by
  obtain ⟨horizontal, checks⟩ := Bool.and_eq_true_iff.mp accepted
  obtain ⟨ab, hab, hspan⟩ :=
    checkChain_covers X monoX (slices.map fun sl => (sl.xLo, sl.xHi)) wpos horizontal hx
  obtain ⟨sl, hsl, rfl⟩ := List.mem_map.mp hab
  have hs : checkSlice rows height sl = true := List.all_eq_true.mp checks sl hsl
  obtain ⟨spanning, vertical⟩ := Bool.and_eq_true_iff.mp hs
  obtain ⟨cd, hcd, hvert⟩ :=
    checkChain_covers Y monoY (sl.vertical.map fun c => (c.yLo, c.yHi)) hpos vertical hy
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hcd
  have cgood : c ∈ rows ∧ c.xLo ≤ sl.xLo ∧ sl.xHi ≤ c.xHi :=
    of_decide_eq_true (List.all_eq_true.mp spanning c hc)
  exact ⟨c, cgood.1, ⟨(monoX.monotone cgood.2.1).trans hspan.1,
    hspan.2.trans (monoX.monotone cgood.2.2)⟩, hvert⟩

/-- A dyadic rectangle with denominator powers allowed to differ by axis
and from other rows. The upper index is always the successor of the lower. -/
structure DyadicRect where
  xDepth : ℕ
  xIndex : ℕ
  yDepth : ℕ
  yIndex : ℕ
  deriving DecidableEq, Repr

def DyadicRect.validAt (Dx Dy : ℕ) (c : DyadicRect) : Bool :=
  decide (c.xDepth ≤ Dx ∧ c.yDepth ≤ Dy ∧
    c.xIndex < 2 ^ c.xDepth ∧ c.yIndex < 2 ^ c.yDepth)

def DyadicRect.normalize (Dx Dy : ℕ) (c : DyadicRect) : GridRect where
  xLo := c.xIndex * 2 ^ (Dx - c.xDepth)
  xHi := (c.xIndex + 1) * 2 ^ (Dx - c.xDepth)
  yLo := c.yIndex * 2 ^ (Dy - c.yDepth)
  yHi := (c.yIndex + 1) * 2 ^ (Dy - c.yDepth)

def checkDyadicCover (Dx Dy : ℕ) (rows : List DyadicRect) (slices : List GridSlice) : Bool :=
  rows.all (DyadicRect.validAt Dx Dy) &&
    checkGridCover (rows.map (DyadicRect.normalize Dx Dy)) (2 ^ Dx) (2 ^ Dy) slices

section OrderedField

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def gridCoord (den index : ℕ) : K := (index : K) / (den : K)

theorem gridCoord_strictMono {den : ℕ} (positive : 0 < den) :
    StrictMono (gridCoord (K := K) den) := by
  intro a b hab
  exact (div_lt_div_iff_of_pos_right (Nat.cast_pos.mpr positive)).2 (Nat.cast_lt.mpr hab)

private theorem dyadicCoord_rescale {depth top : ℕ} (h : depth ≤ top) (i : ℕ) :
    gridCoord (K := K) (2 ^ top) (i * 2 ^ (top - depth)) =
      gridCoord (2 ^ depth) i := by
  have power : (2 : ℕ) ^ top = 2 ^ depth * 2 ^ (top - depth) := by
    rw [← pow_add, Nat.add_sub_of_le h]
  have posFactor : (0 : ℕ) < 2 ^ (top - depth) := pow_pos (by decide : 0 < (2 : ℕ)) _
  simp only [gridCoord, power, Nat.cast_mul]
  exact mul_div_mul_right _ _ ((Nat.cast_pos.mpr posFactor : (0 : K) < _).ne')

def InDyadicRect (c : DyadicRect) (x y : K) : Prop :=
  x ∈ Set.Icc (gridCoord (2 ^ c.xDepth) c.xIndex)
      (gridCoord (2 ^ c.xDepth) (c.xIndex + 1)) ∧
  y ∈ Set.Icc (gridCoord (2 ^ c.yDepth) c.yIndex)
      (gridCoord (2 ^ c.yDepth) (c.yIndex + 1))

/-- Finite accepted slices cover the whole closed unit square, with
the original dyadic rectangle as witness. No density or floor lemma is used. -/
theorem checkDyadicCover_covers {Dx Dy : ℕ} {rows : List DyadicRect} {slices : List GridSlice}
    (accepted : checkDyadicCover Dx Dy rows slices = true)
    {x y : K} (hx : x ∈ Set.Icc 0 1) (hy : y ∈ Set.Icc 0 1) :
    ∃ c ∈ rows, InDyadicRect c x y := by
  obtain ⟨valid, cover⟩ := Bool.and_eq_true_iff.mp accepted
  have px : 0 < (2 : ℕ) ^ Dx := pow_pos (by decide : 0 < (2 : ℕ)) _
  have py : 0 < (2 : ℕ) ^ Dy := pow_pos (by decide : 0 < (2 : ℕ)) _
  have nx : ((2 ^ Dx : ℕ) : K) ≠ 0 := (Nat.cast_pos.mpr px).ne'
  have ny : ((2 ^ Dy : ℕ) : K) ≠ 0 := (Nat.cast_pos.mpr py).ne'
  have hx' : x ∈ Set.Icc (gridCoord (2 ^ Dx) 0) (gridCoord (2 ^ Dx) (2 ^ Dx)) := by
    simpa only [gridCoord, Nat.cast_zero, zero_div, div_self nx] using hx
  have hy' : y ∈ Set.Icc (gridCoord (2 ^ Dy) 0) (gridCoord (2 ^ Dy) (2 ^ Dy)) := by
    simpa only [gridCoord, Nat.cast_zero, zero_div, div_self ny] using hy
  obtain ⟨g, hg, hgrid⟩ :=
    checkGridCover_covers (gridCoord (K := K) (2 ^ Dx)) (gridCoord (K := K) (2 ^ Dy))
      (gridCoord_strictMono px) (gridCoord_strictMono py) px py cover hx' hy'
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hg
  have hgood : c.xDepth ≤ Dx ∧ c.yDepth ≤ Dy ∧
      c.xIndex < 2 ^ c.xDepth ∧ c.yIndex < 2 ^ c.yDepth :=
    of_decide_eq_true (List.all_eq_true.mp valid c hc)
  refine ⟨c, hc, ?_⟩
  simpa only [InDyadicRect, DyadicRect.normalize, dyadicCoord_rescale hgood.1,
    dyadicCoord_rescale hgood.2.1] using hgrid

/-- Eliminate the cover into any pointwise predicate. Rows can carry arbitrary
additional certificate data, and no uniqueness assertion is needed on seams. -/
theorem checkDyadicCover_elim {ρ : Type*} (rect : ρ → DyadicRect)
    {Dx Dy : ℕ} {rows : List ρ} {slices : List GridSlice} {P : K → K → Prop}
    (accepted : checkDyadicCover Dx Dy (rows.map rect) slices = true)
    (rowRule : ∀ r ∈ rows, ∀ a b : K, InDyadicRect (rect r) a b → P a b)
    {x y : K} (hx : x ∈ Set.Icc 0 1) (hy : y ∈ Set.Icc 0 1) : P x y := by
  obtain ⟨c, hc, hxy⟩ := checkDyadicCover_covers accepted hx hy
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hc
  exact rowRule r hr x y hxy

end OrderedField

end RKCert.ReviewedNative.PolynomialCertificate
