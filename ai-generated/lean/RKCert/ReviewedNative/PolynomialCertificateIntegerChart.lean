module

public import RKCert.ReviewedNative.PolynomialCertificateRationalChart

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Kernel-reducible homogeneous integer Taylor certificates

The searches use only integer additions and multiplications, not rational
normalization at every step. All four corner bounds have exactly the same
positive multiplier; the equality with the original polynomial chart is
proved for every coefficient index. -/

namespace RKCert.ReviewedNative.PolynomialCertificate

open Polynomial
open scoped Polynomial

structure IntegerColumns where
  base : List ℤ
  inS : List ℤ
  inT : List ℤ
  inST : List ℤ
  deriving Repr

def IntegerColumns.toRat (v : IntegerColumns) : RationalColumns where
  base := v.base.map (fun i : ℤ => (i : ℚ))
  inS := v.inS.map (fun i : ℤ => (i : ℚ))
  inT := v.inT.map (fun i : ℤ => (i : ℚ))
  inST := v.inST.map (fun i : ℤ => (i : ℚ))

abbrev IntegerColumns.Within (v : IntegerColumns) (w : ℕ) : Prop :=
  v.base.length ≤ w ∧ v.inS.length ≤ w ∧ v.inT.length ≤ w ∧ v.inST.length ≤ w

/-- Denominator-cleared Horner recurrence. Its scale is d^(length cs). -/
def homogeneousJet (z d : ℤ) : List ℤ → ℕ → ℤ
  | [] => fun _ => 0
  | a :: cs => fun j =>
    match j with
    | 0 => a * d ^ (cs.length + 1) + z * homogeneousJet z d cs 0
    | k + 1 => d * homogeneousJet z d cs k + z * homogeneousJet z d cs (k + 1)

theorem homogeneousJet_cast (z d : ℤ) (hd : d ≠ 0) (cs : List ℤ) (j : ℕ) :
    (homogeneousJet z d cs j : ℚ) =
      (d : ℚ) ^ cs.length * taylorEntry ((z : ℚ) / (d : ℚ)) (cs.map (fun i : ℤ => (i : ℚ))) j := by
  have hq : (d : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hd
  induction cs generalizing j with
  | nil => simp [homogeneousJet, taylorEntry]
  | cons a cs ih =>
    cases j <;>
      simp only [homogeneousJet, List.length_cons, List.map_cons, taylorEntry, Int.cast_add,
        Int.cast_mul, Int.cast_pow, ih, pow_succ] <;>
      field_simp [hq] <;> ring

/-- Pad only the scale, not the coefficient arrays. -/
def integerJet (width : ℕ) (z d : ℤ) (cs : List ℤ) (j : ℕ) : ℤ :=
  d ^ (width - cs.length) * homogeneousJet z d cs j

theorem integerJet_cast {width : ℕ} (z d : ℤ) (hd : d ≠ 0)
    (cs : List ℤ) (hc : cs.length ≤ width) (j : ℕ) :
    (integerJet width z d cs j : ℚ) =
      (d : ℚ) ^ width * taylorEntry ((z : ℚ) / (d : ℚ)) (cs.map (fun i : ℤ => (i : ℚ))) j := by
  rw [integerJet, Int.cast_mul, Int.cast_pow, homogeneousJet_cast z d hd,
    ← mul_assoc, ← pow_add, Nat.sub_add_cancel hc]

/-- Integer rational-grid points: sx/dx, sy/dy are the two parameters and
z/d is the polynomial's (centered) Taylor point. -/
def integerCorner (v : IntegerColumns) (width : ℕ) (z d dx dy sx sy : ℤ) (j : ℕ) : ℤ :=
  dx * dy * integerJet width z d v.base j +
  sx * dy * integerJet width z d v.inS j +
  dx * sy * integerJet width z d v.inT j +
  sx * sy * integerJet width z d v.inST j

theorem integerCorner_cast (v : IntegerColumns) (width : ℕ) (hw : v.Within width)
    (z d dx dy sx sy : ℤ) (hd : d ≠ 0) (hx : dx ≠ 0) (hy : dy ≠ 0) (j : ℕ) :
    (integerCorner v width z d dx dy sx sy j : ℚ) =
      ((d : ℚ) ^ width * dx * dy) *
       chartJet v.toRat ((z : ℚ) / d) j ((sx : ℚ) / dx) ((sy : ℚ) / dy) := by
  have hd' : (d : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hd
  have hx' : (dx : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hx
  have hy' : (dy : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hy
  simp only [integerCorner, Int.cast_add, Int.cast_mul, integerJet_cast z d hd _ hw.1,
    integerJet_cast z d hd _ hw.2.1, integerJet_cast z d hd _ hw.2.2.1,
    integerJet_cast z d hd _ hw.2.2.2, chartJet, biForm, IntegerColumns.toRat, Rat.cast_id]
  field_simp [hx', hy', hd']
  <;> ring

structure IntegerQuad where
  ll : ℤ
  lu : ℤ
  ul : ℤ
  uu : ℤ
  deriving Repr

def IntegerQuad.low (q : IntegerQuad) : ℤ := min (min q.ll q.lu) (min q.ul q.uu)

def IntegerQuad.high (q : IntegerQuad) : ℤ := max (max q.ll q.lu) (max q.ul q.uu)

private theorem IntegerQuad.mem_ll (q : IntegerQuad) : q.ll ∈ Set.Icc q.low q.high :=
  ⟨(min_le_left _ _).trans (min_le_left _ _), (le_max_left _ _).trans (le_max_left _ _)⟩

private theorem IntegerQuad.mem_lu (q : IntegerQuad) : q.lu ∈ Set.Icc q.low q.high :=
  ⟨(min_le_left _ _).trans (min_le_right _ _), (le_max_right _ _).trans (le_max_left _ _)⟩

private theorem IntegerQuad.mem_ul (q : IntegerQuad) : q.ul ∈ Set.Icc q.low q.high :=
  ⟨(min_le_right _ _).trans (min_le_left _ _), (le_max_left _ _).trans (le_max_right _ _)⟩

private theorem IntegerQuad.mem_uu (q : IntegerQuad) : q.uu ∈ Set.Icc q.low q.high :=
  ⟨(min_le_right _ _).trans (min_le_right _ _), (le_max_right _ _).trans (le_max_right _ _)⟩

def rowXDen (r : DyadicRect) : ℤ := ((2 ^ r.xDepth : ℕ) : ℤ)
def rowYDen (r : DyadicRect) : ℤ := ((2 ^ r.yDepth : ℕ) : ℤ)

def integerQuad (v : IntegerColumns) (width : ℕ) (z d : ℤ) (r : DyadicRect) (j : ℕ) :
    IntegerQuad :=
  let val := fun x y => integerCorner v width z d (rowXDen r) (rowYDen r) (x : ℤ) (y : ℤ) j
  ⟨val (r.xIndex : ℕ) (r.yIndex : ℕ),
   val (r.xIndex : ℕ) (r.yIndex + 1 : ℕ),
   val (r.xIndex + 1 : ℕ) (r.yIndex : ℕ),
   val (r.xIndex + 1 : ℕ) (r.yIndex + 1 : ℕ)⟩

def rowScale (width : ℕ) (d : ℤ) (r : DyadicRect) : ℚ :=
  (d : ℚ) ^ width * (rowXDen r : ℚ) * (rowYDen r : ℚ)

private theorem rowXDen_pos (r : DyadicRect) : 0 < rowXDen r :=
  Int.natCast_pos.mpr (pow_pos (by decide : 0 < (2 : ℕ)) _)

private theorem rowYDen_pos (r : DyadicRect) : 0 < rowYDen r :=
  Int.natCast_pos.mpr (pow_pos (by decide : 0 < (2 : ℕ)) _)

theorem rowScale_pos (width : ℕ) {d : ℤ} (hd : 0 < d) (r : DyadicRect) : 0 < rowScale width d r :=
  mul_pos (mul_pos (pow_pos (Int.cast_pos.mpr hd) _) (Int.cast_pos.mpr (rowXDen_pos r)))
    (Int.cast_pos.mpr (rowYDen_pos r))

private theorem in_scaled_range (scale : ℚ) (h : 0 < scale) {x : ℚ} {z l u : ℤ}
    (hz : (z : ℚ) = scale * x) (hlu : z ∈ Set.Icc l u) :
    x ∈ Set.Icc ((l : ℚ) / scale) ((u : ℚ) / scale) := by
  constructor
  · apply (div_le_iff₀ h).2
    rw [mul_comm, ← hz]
    exact Int.cast_le.mpr hlu.1
  · apply (le_div_iff₀ h).2
    rw [mul_comm, ← hz]
    exact Int.cast_le.mpr hlu.2

theorem integerQuad_corners (v : IntegerColumns) (width : ℕ) (hw : v.Within width)
    (z d : ℤ) (hd : 0 < d) (r : DyadicRect) (j : ℕ) :
    let q := integerQuad v width z d r j
    chartJetCornersIn v.toRat r ((z : ℚ) / d) j
      ((q.low : ℚ) / rowScale width d r) ((q.high : ℚ) / rowScale width d r) := by
  let q := integerQuad v width z d r j
  have eqn (a b : ℕ) := integerCorner_cast v width hw z d (rowXDen r) (rowYDen r)
    (a : ℤ) (b : ℤ) hd.ne' (rowXDen_pos r).ne' (rowYDen_pos r).ne' j
  have hp := rowScale_pos width hd r
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply in_scaled_range _ hp (z := q.ll) _ q.mem_ll
    simpa [q, integerQuad, DyadicRect.left, DyadicRect.bottom, gridCoord, rowScale,
      rowXDen, rowYDen] using eqn r.xIndex r.yIndex
  · apply in_scaled_range _ hp (z := q.lu) _ q.mem_lu
    simpa [q, integerQuad, DyadicRect.left, DyadicRect.top, gridCoord, rowScale,
      rowXDen, rowYDen] using eqn r.xIndex (r.yIndex + 1)
  · apply in_scaled_range _ hp (z := q.ul) _ q.mem_ul
    simpa [q, integerQuad, DyadicRect.right, DyadicRect.bottom, gridCoord, rowScale,
      rowXDen, rowYDen] using eqn (r.xIndex + 1) r.yIndex
  · apply in_scaled_range _ hp (z := q.uu) _ q.mem_uu
    simpa [q, integerQuad, DyadicRect.right, DyadicRect.top, gridCoord, rowScale,
      rowXDen, rowYDen] using eqn (r.xIndex + 1) (r.yIndex + 1)

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

noncomputable def integerScaledChart (v : IntegerColumns) (width : ℕ) (d : ℤ)
    (r : DyadicRect) (s t : K) : K[X] :=
  C (rowScale width d r : K) * rationalChart v.toRat s t

theorem integerScaledChart_taylor_coeff (v : IntegerColumns) (width : ℕ) (hw : v.Within width)
    (z d : ℤ) (hd : 0 < d) (r : DyadicRect) (j : ℕ) {s t : K} (h : InDyadicRect r s t) :
    let q := integerQuad v width z d r j
    ((integerScaledChart v width d r s t).taylor (((z : ℚ) / d : ℚ) : K)).coeff j ∈
      Set.Icc (q.low : K) (q.high : K) := by
  let q := integerQuad v width z d r j
  let scale := rowScale width d r
  have hs : (0 : K) < (scale : K) := Rat.cast_pos.mpr (rowScale_pos width hd r)
  have hl := rationalChart_coeff_mem_of_corners v.toRat r ((z : ℚ) / d) j
    ((q.low : ℚ) / scale) ((q.high : ℚ) / scale) (integerQuad_corners v width hw z d hd r j) h
  have lo : (q.low : K) / (scale : K) ≤
      ((rationalChart v.toRat s t).taylor (((z : ℚ) / d : ℚ) : K)).coeff j := by
    simpa using hl.1
  have hi : ((rationalChart v.toRat s t).taylor (((z : ℚ) / d : ℚ) : K)).coeff j ≤
      (q.high : K) / (scale : K) := by simpa using hl.2
  change ((C (scale : K) * rationalChart v.toRat s t).taylor _).coeff j ∈ Set.Icc (q.low : K) (q.high : K)
  rw [taylor_mul, taylor_C, coeff_C_mul, mul_comm]
  exact ⟨(div_le_iff₀ hs).mp lo, (le_div_iff₀ hs).mp hi⟩

end RKCert.ReviewedNative.PolynomialCertificate
