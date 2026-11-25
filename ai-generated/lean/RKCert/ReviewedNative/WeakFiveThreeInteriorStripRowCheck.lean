module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorStripInteger

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Bounded per-row strip decisions

The cached rational defect ends are individually checked against the
actual closed rectangle. Strict coefficient decisions use only integers.
The eight small power coefficients are shared in each edge evaluation.
-/
namespace RKCert.ReviewedNative.ThreeInteriorPencil

open Polynomial RKCert.ReviewedNative.PolynomialCertificate
open RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
open scoped Polynomial BigOperators

structure StripDefectCache where
  numerator : ℤ
  denominator : ℕ

def StripDefectCache.value (w : StripDefectCache) : ℚ :=
  (w.numerator:ℚ)/(w.denominator:ℚ)

structure StripRowPacket where
  row : ThreeInteriorCell
  lowDefect : StripDefectCache
  highDefect : StripDefectCache

def StripRowPacket.cache (p : StripRowPacket) : Bool → StripDefectCache
  | false => p.lowDefect
  | true => p.highDefect

def validStripCache (p : StripRowPacket) (bias : Bool) : Prop :=
  0 < (p.cache bias).denominator ∧ (p.cache bias).value = templateDefect p.row bias

instance (p : StripRowPacket) (bias : Bool) : Decidable (validStripCache p bias) := by
  unfold validStripCache
  infer_instance

def checkStripCache (p : StripRowPacket) : Bool :=
  decide (validStripCache p false ∧ validStripCache p true)

def stripShape (r : ThreeInteriorCell) : Prop :=
  r.rect.xIndex < 2^r.rect.xDepth ∧ r.rect.yIndex < 2^r.rect.yDepth ∧
  (∀ i, r.low i < r.high i) ∧ (∀ i, r.high i ≤ 8192) ∧
  ∀ i j, i < j → r.high i < r.low j

instance (r : ThreeInteriorCell) : Decidable (stripShape r) := by
  unfold stripShape
  infer_instance

def checkStripShape (r : ThreeInteriorCell) : Bool := decide (stripShape r)

def fastBernstein {N : ℕ} (T : SparseDetTemplate N) (d s x : ℕ) : Array ℤ :=
  let p : Array ℤ := .ofFn (fun j : Fin 8 => clearedPower T d s x j.val)
  .ofFn (fun k : Fin 8 => ∑ j ∈ Finset.range 8, (p.getD j 0)*(bernWeightZ k.val j : ℤ))

theorem fastBernstein_get {N : ℕ} (T : SparseDetTemplate N) (d s x : ℕ) (k : Fin 8) :
    (fastBernstein T d s x).getD k.val 0 = clearedBernstein T d s x k.val := by
  simp only [fastBernstein,Array.getD_eq_getD_getElem?,Array.getElem?_ofFn,dif_pos k.isLt,
    Option.getD_some,clearedBernstein]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [dif_pos (Finset.mem_range.mp hj),Option.getD_some]

def cachedCombineZ (sign : ℤ) (d : StripDefectCache) (D7 D6 : ℤ) : ℤ :=
  sign*((d.denominator:ℤ)*D7+d.numerator*D6)

def checkSingleEdge (p : StripRowPacket) (upper : Bool) (i : Fin 7) : Bool :=
  let r := p.row
  let x := edgeNumerator r upper i
  if x = 0 ∨ x = 8192 then true else
    let d := 2^r.rect.xDepth
    let s := r.rect.xIndex
    let D7 := fastBernstein publishedTemplate7 d s x
    let D6 := fastBernstein publishedTemplate6 d s x
    let sg := edgeSense upper i
    (List.finRange 8).all fun k =>
      decide (0 < cachedCombineZ sg (p.cache false) (D7.getD k.val 0) (D6.getD k.val 0) ∧
        0 < cachedCombineZ sg (p.cache true) (D7.getD k.val 0) (D6.getD k.val 0))

def checkEdgePair (p : StripRowPacket) (i : Fin 7) : Bool :=
  checkSingleEdge p false i && checkSingleEdge p true i

def checkStripPacket (p : StripRowPacket) : Bool :=
  checkStripShape p.row && (checkStripCache p && (List.finRange 7).all (checkEdgePair p))

theorem checkStripPacket_intro {p : StripRowPacket}
    (shape : checkStripShape p.row = true) (cache : checkStripCache p = true)
    (edges : ∀ i, checkEdgePair p i = true) : checkStripPacket p = true := by
  have h : (List.finRange 7).all (checkEdgePair p) = true := List.all_eq_true.mpr (fun i _ => edges i)
  rw [checkStripPacket, shape, cache, h] <;> rfl

private theorem cachedCoefficient_sound {p : StripRowPacket} (upper : Bool) (i : Fin 7)
    (bias : Bool) (k : Fin 8) (valid : validStripCache p bias)
    (z : 0 < cachedCombineZ (edgeSense upper i) (p.cache bias)
      (clearedBernstein publishedTemplate7 (2^p.row.rect.xDepth) p.row.rect.xIndex
        (edgeNumerator p.row upper i) k.val)
      (clearedBernstein publishedTemplate6 (2^p.row.rect.xDepth) p.row.rect.xIndex
        (edgeNumerator p.row upper i) k.val)) :
    0 < finiteStripCoefficient p.row upper i bias k := by
  let r := p.row
  let d := p.cache bias
  let s := 2^r.rect.xDepth
  let j := r.rect.xIndex
  let x := edgeNumerator r upper i
  have dp : (0:ℚ) < (d.denominator:ℚ) := Nat.cast_pos.mpr valid.1
  have sp : 0 < s := pow_pos (by decide) _
  have nm : (d.numerator:ℚ) = templateDefect r bias*(d.denominator:ℚ) :=
    (div_eq_iff dp.ne').mp valid.2
  have zp : 0 < (cachedCombineZ (edgeSense upper i) d
      (clearedBernstein publishedTemplate7 s j x k.val)
      (clearedBernstein publishedTemplate6 s j x k.val) : ℚ) := by exact_mod_cast z
  have eq :
      (cachedCombineZ (edgeSense upper i) d
        (clearedBernstein publishedTemplate7 s j x k.val)
        (clearedBernstein publishedTemplate6 s j x k.val) : ℚ) =
      (bernFactor s*(d.denominator:ℚ))*finiteStripCoefficient r upper i bias k := by
    simp only [cachedCombineZ,Int.cast_mul,Int.cast_add,Int.cast_natCast]
    rw [nm,clearedBernstein_cast publishedTemplate7 le_rfl _ _ _ _ sp,
      clearedBernstein_cast publishedTemplate6 (by decide) _ _ _ _ sp,semantic_signed_coefficient]
    ring
  rw [eq] at zp
  have mulp : 0 < bernFactor s*(d.denominator:ℚ) := by
    unfold bernFactor powerFactor
    exact mul_pos (mul_pos (by decide) (mul_pos (pow_pos (by decide) _)
      (pow_pos (Nat.cast_pos.mpr sp) _))) dp
  exact (mul_pos_iff_of_pos_left mulp).mp zp

private theorem single_edge_sound {p : StripRowPacket} {upper : Bool} {i : Fin 7}
    (h : checkSingleEdge p upper i = true)
    (n0 : edgeNumerator p.row upper i ≠ 0) (n1 : edgeNumerator p.row upper i ≠ 8192)
    (bias : Bool) (k : Fin 8) (valid : validStripCache p bias) :
    0 < finiteStripCoefficient p.row upper i bias k := by
  simp only [checkSingleEdge,if_neg (show ¬ (edgeNumerator p.row upper i = 0 ∨
    edgeNumerator p.row upper i = 8192) from fun e => e.elim n0 n1)] at h
  have kpos := of_decide_eq_true (List.all_eq_true.mp h k (by simp))
  apply cachedCoefficient_sound _ _ _ _ valid
  cases bias
  · simpa only [fastBernstein_get] using kpos.1
  · simpa only [fastBernstein_get] using kpos.2

/-- Every accepted finite row packet gives the frozen semantic receipt,
including all strict coefficients and the literal shape guards. -/
theorem stripRows_of_packet_checks {P : List StripRowPacket}
    (accepted : P.all checkStripPacket = true) :
    ThreeInteriorFiniteStripRows (P.map StripRowPacket.row) := by
  have test (p : StripRowPacket) (hp : p ∈ P) := List.all_eq_true.mp accepted p hp
  have shape {r : ThreeInteriorCell} (hr : r ∈ P.map StripRowPacket.row) : stripShape r := by
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hr
    exact of_decide_eq_true (Bool.and_eq_true_iff.mp (test p hp)).1
  refine ⟨fun r hr => (shape hr).1,fun r hr => (shape hr).2.1,
    fun r hr => (shape hr).2.2.1, fun r hr => (shape hr).2.2.2.1,
    fun r hr _ _ h => (shape hr).2.2.2.2 _ _ h,?_⟩
  intro r hr upper i n0 n1 bias k
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hr
  have other := (Bool.and_eq_true_iff.mp (test p hp)).2
  have packs := Bool.and_eq_true_iff.mp other
  have cached : validStripCache p false ∧ validStripCache p true := of_decide_eq_true packs.1
  have eis := Bool.and_eq_true_iff.mp (List.all_eq_true.mp packs.2 i (by simp))
  cases upper <;> cases bias
  · exact single_edge_sound eis.1 n0 n1 false k cached.1
  · exact single_edge_sound eis.1 n0 n1 true k cached.2
  · exact single_edge_sound eis.2 n0 n1 false k cached.1
  · exact single_edge_sound eis.2 n0 n1 true k cached.2

end RKCert.ReviewedNative.ThreeInteriorPencil
