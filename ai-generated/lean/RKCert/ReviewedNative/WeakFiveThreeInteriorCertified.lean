module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorSevenRule
public import RKCert.ReviewedNative.WeakFiveThreeInteriorLocalizer
public import RKCert.ReviewedNative.PolynomialCertificateDyadicCover
public import Mathlib.Order.Preorder.Finite
public import Mathlib.Data.Fin.VecNotation

import Mathlib.Tactic.Choose

@[expose] public section

/-! # Three-interior full-case handoff to the released rational certificate

The nine surviving words and their port signs are fixed, not per-cell or
per-instance choices. The root-strip consumer transports the *actual* split
sites (in their physical word order); it never uses a numerically selected root.
The full table is kept as an explicit finite receipt, not duplicated here.
-/

namespace RKCert.ReviewedNative.OrderedPolynomialSignStrips

open Polynomial RKCert.ReviewedNative.OrderedRootGapSaturation

universe u
variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Saturated sign strips contain the actual ordered split roots. This also
works for closed strips whose endpoint can itself be a root. -/
theorem SignStrips.contains_actual_sites {n : ℕ} {F : K[X]} {l h b : Fin n → K}
    (H : SignStrips F l h) (fn : F ≠ 0) (deg : F.natDegree ≤ n)
    (ord : StrictMono b) (roots : ∀ j, F.IsRoot (b j)) :
    ∀ i, b i ∈ Set.Icc (l i) (h i) := by
  classical
  obtain ⟨E, x, xord, box, xroot⟩ := H.exists_roots
  let f : Fin n → E.carrier := E.embed ∘ b
  let P := F.map E.embed
  have ford : StrictMono f := E.mono.comp ord
  have pn : P ≠ 0 := Polynomial.map_ne_zero fn
  have pd : P.natDegree ≤ (Finset.univ : Finset (Fin n)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact natDegree_map_le.trans deg
  have fr (i : Fin n) : P.IsRoot (f i) := by
    change (F.map E.embed).eval (E.embed (b i)) = 0
    have r : F.eval (b i) = 0 := roots i
    rw [Polynomial.eval_map_apply, r, map_zero]
  have fact : P = C P.leadingCoeff * indexedHull f Finset.univ :=
    factor_eq_of_indexed_roots f Finset.univ ford.injective (fun i _ => fr i) pd
  have index (i : Fin n) : ∃ j, f j = x i := by
    have z : P.eval (x i) = 0 := xroot i
    rw [fact, eval_mul, eval_C] at z
    have hz : (indexedHull f Finset.univ).IsRoot (x i) :=
      (mul_eq_zero.mp z).resolve_left (leadingCoeff_ne_zero.mpr pn)
    obtain ⟨j, _, h⟩ := indexedHull_root_index f hz
    exact ⟨j, h⟩
  choose rank hr using index
  have rank_order : StrictMono rank := by
    intro i j ij
    apply ford.lt_iff_lt.mp
    rw [hr i, hr j]
    exact xord ij
  have rank_id : rank = id := rank_order.eq_id
  intro i
  have eq : E.embed (b i) = x i := by
    simpa only [rank_id, id_eq, f, Function.comp_apply] using hr i
  have bounds := box i
  rw [← eq] at bounds
  exact ⟨E.mono.le_iff_le.mp bounds.1, E.mono.le_iff_le.mp bounds.2⟩

end RKCert.ReviewedNative.OrderedPolynomialSignStrips

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

open Polynomial RKCert.ReviewedNative.WeakFive16
open RKCert.ReviewedNative.OrderedPolynomialSignStrips RKCert.ReviewedNative.OrderedRootGapSaturation
open RKCert.ReviewedNative.FiniteGaussianNodalLift
open RKCert.ReviewedNative.PolynomialCertificate

universe u
variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- In the literal order of the released sign receipt. -/
inductive ThreeInteriorWord
  | w0 | w1 | w2 | w3 | w4 | w5 | w6 | w7 | w8
  deriving DecidableEq

def ThreeInteriorWord.labels : ThreeInteriorWord → Fin 7 → ThreeInteriorSite
  | .w0 => ![.inl 0, .inr 3, .inl 1, .inr 1, .inr 2, .inl 2, .inr 0]  -- 1z2ah3u
  | .w1 => ![.inl 0, .inr 3, .inl 1, .inr 2, .inr 1, .inl 2, .inr 0]  -- 1z2ha3u
  | .w2 => ![.inr 2, .inl 0, .inr 3, .inl 1, .inr 0, .inl 2, .inr 1]  -- h1z2u3a
  | .w3 => ![.inr 2, .inl 0, .inr 3, .inl 1, .inr 1, .inl 2, .inr 0]  -- h1z2a3u
  | .w4 => ![.inr 3, .inl 0, .inr 1, .inl 1, .inr 2, .inl 2, .inr 0]  -- z1a2h3u
  | .w5 => ![.inr 3, .inl 0, .inr 2, .inl 1, .inr 0, .inl 2, .inr 1]  -- z1h2u3a
  | .w6 => ![.inr 3, .inl 0, .inr 2, .inl 1, .inr 1, .inl 2, .inr 0]  -- z1h2a3u
  | .w7 => ![.inr 3, .inl 0, .inr 1, .inr 2, .inl 1, .inr 0, .inl 2]  -- z1ah2u3
  | .w8 => ![.inr 3, .inl 0, .inr 2, .inr 1, .inl 1, .inr 0, .inl 2]  -- z1ha2u3

def ThreeInteriorWord.port : ThreeInteriorWord → ThreeInteriorPort
  | .w0 | .w1 => .l1
  | .w2 | .w5 => .l2
  | .w3 => .r2
  | .w4 => .la
  | .w6 => .rh
  | .w7 | .w8 => .r1

def ThreeInteriorWord.positive : ThreeInteriorWord → Bool
  | .w3 | .w7 | .w8 => true
  | _ => false

def ThreeInteriorWord.sites (w : ThreeInteriorWord) (r : Fin 3 → K) (m : Fin 4 → K) :
    Fin 7 → K := threeInteriorSites r m ∘ w.labels

/-- One literal 18-integer row: four dyadic coordinates, followed by
the seven pairs of integer endpoint numerators. -/
structure ThreeInteriorCell where
  rect : DyadicRect
  low : Fin 7 → ℕ
  high : Fin 7 → ℕ

def ThreeInteriorCell.lowCoord (c : ThreeInteriorCell) (i : Fin 7) : K :=
  gridCoord 8192 (c.low i)

def ThreeInteriorCell.highCoord (c : ThreeInteriorCell) (i : Fin 7) : K :=
  gridCoord 8192 (c.high i)

def ThreeInteriorCell.contains (c : ThreeInteriorCell) (v : Fin 7 → K) : Prop :=
  ∀ i, v i ∈ Set.Icc (c.lowCoord i) (c.highCoord i)

/-- Closed full-domain cover and exact finite localizer vertex receipts.
The box's coordinates are gamma, then the optional extra ratio, then
the three root ratios, merely permuting the released checker's corners. -/
structure ThreeInteriorFiniteTable (rows : List ThreeInteriorCell)
    (D J : ℕ) (slices : List GridSlice) where
  coverage : checkDyadicCover D J (rows.map ThreeInteriorCell.rect) slices = true
  low : (c : ThreeInteriorCell) → (w : ThreeInteriorWord) → Fin (w.port.count+1) → ℚ
  high : (c : ThreeInteriorCell) → (w : ThreeInteriorWord) → Fin (w.port.count+1) → ℚ
  corners : ∀ c ∈ rows, ∀ w : ThreeInteriorWord, ∀ a : Fin (w.port.count+1) → Bool,
    threeInteriorSigned w.positive (threeInteriorLocalizer w.port (vertex (low c w) (high c w) a))

/-- Target of the published stopped-eraser order reduction. This exact
structural obligation is separate from the finite rectangle arithmetic. -/
def ThreeInteriorOrderReceipt : Prop :=
  ∀ (s : K) (r : Fin 3 → K) (m : Fin 4 → K), ThreeInteriorNormalized s r m →
    ∃ w : ThreeInteriorWord, StrictMono (w.sites r m)

/-- Target of the Rayleigh-pencil and bivariate Bernstein bracket port.
It asks only for a genuine compact defect parameter, the split degree-seven
polynomial, and universal strip facts on the rows containing that parameter. -/
def ThreeInteriorPencilReceipt (rows : List ThreeInteriorCell) : Prop :=
  ∀ (s : K) (r : Fin 3 → K) (m : Fin 4 → K) (w : ThreeInteriorWord),
    ThreeInteriorNormalized s r m → StrictMono (w.sites r m) →
    ∀ μ : ThreeInteriorSite → K, (∀ i, 0 < μ i) →
    ExactRule (threeInteriorMoment s) Finset.univ (threeInteriorSites r m) μ 12 →
    ∃ (j : K) (F : K[X]), j ∈ Set.Ioo 0 1 ∧ F ≠ 0 ∧ F.natDegree ≤ 7 ∧
      (∀ i, F.IsRoot (w.sites r m i)) ∧
      (∀ c ∈ rows, InDyadicRect c.rect s j → SignStrips F c.lowCoord c.highCoord)

/-- Exactly the monotonicity/ratio-enclosure part of data admission. No
moment is an input: these are algebraic inequalities from the cages. -/
def ThreeInteriorRatioReceipt {rows : List ThreeInteriorCell} {D J : ℕ}
    {slices : List GridSlice} (A : ThreeInteriorFiniteTable rows D J slices) : Prop :=
  ∀ c ∈ rows, ∀ (w : ThreeInteriorWord) (s j : K) (r : Fin 3 → K) (m : Fin 4 → K),
    InDyadicRect c.rect s j →
    (∀ i, r i ∈ Set.Ioo 0 1) → (∀ i, m i ∈ Set.Ioo 0 1) →
    c.contains (w.sites r m) →
    ∀ i, threeInteriorLocalizerArgs w.port s r m i ∈ Set.Icc (A.low c w i : K) (A.high c w i : K)

/-- The single-case bridge is full-domain: against these precisely typed
receipts every literal classifier packet is contradictory over its own
ordered extension, including both orientation seams. -/
theorem no_actual_threeInterior_of_exact_receipts {q Z : K[X]} {c : Fin 5 → K}
    {rows : List ThreeInteriorCell} {D J : ℕ} {slices : List GridSlice}
    (A : ThreeInteriorFiniteTable rows D J slices) (M : Moments q Z c)
    (order : ∀ E : OrderedExtension K, ThreeInteriorOrderReceipt (K := E.carrier))
    (pencil : ∀ E : OrderedExtension K, ThreeInteriorPencilReceipt (K := E.carrier) rows)
    (ratios : ∀ E : OrderedExtension K, ThreeInteriorRatioReceipt (K := E.carrier) A) :
    ThreeInterior q c → False := by
  intro H
  obtain ⟨E, s, r, m, _, _, N, _⟩ := normalized_threeInterior_of_actual M H
  obtain ⟨w, worder⟩ := order E s r m N
  obtain ⟨μ, μpos, law⟩ := N.seven_rule
  obtain ⟨j, F, jp, fn, fd, fr, byStrips⟩ := pencil E s r m w N worder μ μpos law
  obtain ⟨rect, hr, point⟩ := checkDyadicCover_covers A.coverage
    (show s ∈ Set.Icc 0 1 from ⟨N.parameter.1, N.parameter.2.le⟩)
    (show j ∈ Set.Icc 0 1 from ⟨jp.1.le, jp.2.le⟩)
  obtain ⟨row, hrow, hrEq⟩ := List.mem_map.mp hr
  have pt : InDyadicRect row.rect s j := by
    rw [hrEq]
    exact point
  have cages : row.contains (w.sites r m) :=
    (byStrips row hrow pt).contains_actual_sites fn fd worder fr
  have args := ratios E row hrow w s j r m pt N.rootInside N.markInside cages
  have signed := threeInteriorLocalizer_signed_rat_box w.port w.positive args (A.corners row hrow w)
  rw [N.localizer_zero w.port] at signed
  cases pol : w.positive <;>
    exact (lt_irrefl (0 : E.carrier)) (by simpa only [pol, threeInteriorSigned] using signed)

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
