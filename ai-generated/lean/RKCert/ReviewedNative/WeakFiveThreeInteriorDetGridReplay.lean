module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorTemplateTransport
public import Mathlib.LinearAlgebra.Matrix.Determinant.Bird.Correctness
public import Mathlib.Data.Nat.Cast.Field

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Exact integer validation of the 113 determinant-template values

The entries use the literal 12252240 common denominator. The checker uses
the independent division-free Bird algorithm from mathlib, not the Python
Bareiss implementation. Correctness and rational casting are explicit.
-/
namespace RKCert.ReviewedNative.ThreeInteriorPencil

open Polynomial Matrix RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
open scoped Matrix Polynomial BigOperators

def momentBaseZ (k : ℕ) : ℤ := ((12252240 / ((k+2)*(k+3)) : ℕ) : ℤ)

def momentAffineZ (k s : ℕ) : ℤ :=
  momentBaseZ (k+1)+(s:ℤ)*(momentBaseZ k-momentBaseZ (k+1))

def gridMatrixZ (n s x : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j => momentAffineZ (i.val+j.val+1) s-(x:ℤ)*momentAffineZ (i.val+j.val) s

def SparseDetTemplate.valueZ {N : ℕ} (T : SparseDetTemplate N) (s x : ℕ) : ℤ :=
  (T.terms.map fun a => a.2.2*(s:ℤ)^a.1*(x:ℤ)^a.2.1).sum

def gridDetZ (n s x : ℕ) : ℤ := BirdDet.birdDet n (gridMatrixZ n s x).toArray

private theorem denom_divides (i : Fin 15) : (i.val+2)*(i.val+3) ∣ (12252240:ℕ) := by
  fin_cases i <;> decide

private theorem baseZ_cast {k : ℕ} (hk : k ≤ 14) :
    (momentBaseZ k : ℚ) = 12252240 * threeInteriorBaseMoment k := by
  have hd : (k+2)*(k+3) ∣ (12252240 : ℕ) :=
    denom_divides ⟨k, Nat.lt_succ_of_le hk⟩
  have castQuotient :
      (((12252240 : ℕ) / ((k+2)*(k+3)) : ℕ) : ℚ) =
        ((12252240 : ℕ) : ℚ) / ((((k+2)*(k+3)) : ℕ) : ℚ) :=
    Nat.cast_div_charZero (K := ℚ) hd
  calc
    (momentBaseZ k : ℚ) = (((12252240 : ℕ) / ((k+2)*(k+3)) : ℕ) : ℚ) := by
      simp only [momentBaseZ, Int.cast_natCast]
    _ = ((12252240 : ℕ) : ℚ) / ((((k+2)*(k+3)) : ℕ) : ℚ) := castQuotient
    _ = 12252240 * threeInteriorBaseMoment k := by
      simp only [threeInteriorBaseMoment, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, mul_one_div]

private theorem affineZ_cast {k : ℕ} (hk : k ≤ 13) (s : ℕ) :
    (momentAffineZ k s : ℚ) = threeInteriorScaledMoment (s:ℚ) (X^k) := by
  rw [threeInteriorScaledMoment_monomial]
  simp only [momentAffineZ,Int.cast_add, Int.cast_mul, Int.cast_sub,Int.cast_natCast,
    baseZ_cast (by omega : k+1 ≤ 14),baseZ_cast (hk.trans (by decide))]
  ring

private theorem gridMatrixZ_cast {n : ℕ} (hn : n ≤ 7) (s x : ℕ) :
    (gridMatrixZ n s x).map (Int.castRingHom ℚ) = pencilAt n (s:ℚ) (x:ℚ) := by
  ext i j
  have d : i.val+j.val+1 ≤ 13 := by have hi := i.isLt; have hj := j.isLt; omega
  simp only [gridMatrixZ,Matrix.map_apply,Matrix.of_apply,Int.coe_castRingHom,
    Int.cast_sub,Int.cast_mul,Int.cast_natCast,pencilAt,Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul,gramA_apply,gramB_apply,affineZ_cast d,affineZ_cast (by omega : i.val+j.val ≤ 13)]

theorem gridDetZ_cast {n : ℕ} (hn : n ≤ 7) (s x : ℕ) :
    (gridDetZ n s x : ℚ) = determinantAt n (s:ℚ) (x:ℚ) := by
  let A := gridMatrixZ n s x
  have comp : A.det = BirdDet.birdDet n A.toArray := by
    simpa only [Matrix.ofArray_toArray] using BirdDet.det_eq_birdDet A.toArray A.size_toArray
  change (Int.castRingHom ℚ) (BirdDet.birdDet n A.toArray) = _
  rw [← comp,RingHom.map_det]
  change ((gridMatrixZ n s x).map (Int.castRingHom ℚ)).det = _
  rw [gridMatrixZ_cast hn,determinantAt]

theorem SparseDetTemplate.valueZ_cast {N : ℕ} (T : SparseDetTemplate N) (s x : ℕ) :
    (T.valueZ s x : ℚ) = T.value (s:ℚ) (x:ℚ) := by
  unfold SparseDetTemplate.valueZ SparseDetTemplate.value
  change (Int.castRingHom ℚ) ((T.terms.map _).sum) = _
  rw [map_list_sum,List.map_map]
  apply congrArg List.sum
  apply congrArg (fun f : ℕ × ℕ × ℤ → ℚ => T.terms.map f)
  funext a
  simp only [Function.comp_apply,Int.coe_castRingHom,Int.cast_mul,Int.cast_pow,Int.cast_natCast]

set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

namespace DetGridReplayCountdown

open Function

/-- Kernel-visible countdown for the *same* half-open Bird sum. -/
private def sumDown (f : ℕ → ℤ) : ℕ → ℕ → ℤ
  | 0, _ => 0
  | fuel+1, lo => f lo + sumDown f fuel (lo+1)

private theorem sumDown_eq_sumFrom (n lo : ℕ) (f : ℕ → ℤ) :
    sumDown f (n-lo) lo = BirdDet.sumFrom n lo f := by
  induction lo using BirdDet.sumFrom_induct n with
  | step lo hlo ih =>
      have fuel : n-lo = (n-(lo+1))+1 := by omega
      rw [fuel, sumDown, ih, BirdDet.sumFrom_step n lo f hlo]
  | stop lo hlo =>
      rw [Nat.sub_eq_zero_of_le (le_of_not_gt hlo), sumDown, BirdDet.sumFrom_stop n lo f hlo]

private def stepDown (n : ℕ) (A F : ℕ → ℕ → ℤ) (i j : ℕ) : ℤ :=
  -(sumDown (fun k => F k k) (n-(i+1)) (i+1)) * A i j +
    sumDown (fun k => F i k * A k j) (n-(i+1)) (i+1)

private theorem stepDown_eq (n : ℕ) (A : Array ℤ) (F : ℕ → ℕ → ℤ) :
    stepDown n (BirdDet.get n A) F = BirdDet.stepEntry n A F := by
  funext i j
  simp only [stepDown, BirdDet.stepEntry_eq, sumDown_eq_sumFrom]

private def layerDown (n : ℕ) (A : ℕ → ℕ → ℤ) : ℕ → ℕ → ℕ → ℤ
  | 0 => A
  | t+1 => stepDown n A (layerDown n A t)

private theorem layerDown_eq (n : ℕ) (A : Array ℤ) (t : ℕ) :
    layerDown n (BirdDet.get n A) t = (BirdDet.stepEntry n A)^[t] (BirdDet.get n A) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [layerDown, Function.iterate_succ_apply', ih, stepDown_eq]

private def detDown (n : ℕ) (A : ℕ → ℕ → ℤ) : ℤ :=
  match n with
  | 0 => 1
  | t+1 => (-1 : ℤ)^t * layerDown (t+1) A t 0 0

private theorem detDown_eq (n : ℕ) (A : Array ℤ) :
    detDown n (BirdDet.get n A) = BirdDet.birdDet n A := by
  cases n with
  | zero => exact (BirdDet.birdDet_zero A).symm
  | succ t => rw [detDown, BirdDet.birdDet_succ, layerDown_eq]

/-- Reify the original input array only for its propositional lookup proof. -/
private def rowInput (n s x : ℕ) : Array ℤ :=
  Array.ofFn fun k : Fin (n*n) => (gridMatrixZ n s x) k.divNat k.modNat

private theorem rowInput_eq (n s x : ℕ) :
    rowInput n s x = (gridMatrixZ n s x).toArray := by
  let A : Matrix (Fin n) (Fin n) ℤ := gridMatrixZ n s x
  let B : Array ℤ := rowInput n s x
  have sizeB : B.size = n*n := by
    dsimp only [B, rowInput]
    exact Array.size_ofFn
  have repr : Matrix.ofArray B sizeB = A := by
    simpa only [B, rowInput, A] using Matrix.ofArray_ofFn (m := n) (n := n) A
  change B = A.toArray
  exact (Matrix.toArray_ofArray (m := n) (n := n) B sizeB).symm.trans
    (congrArg (fun M : Matrix (Fin n) (Fin n) ℤ => M.toArray) repr)

/-- A direct flat read, including the original behavior outside the flat
index range. In particular it does not test the two coordinates separately. -/
private def readGrid (n s x i j : ℕ) : ℤ :=
  let k := n*i+j
  if k < n*n then
    momentAffineZ (k/n+k%n+1) s - (x:ℤ)*momentAffineZ (k/n+k%n) s
  else 0

private theorem readGrid_eq (n s x i j : ℕ) :
    readGrid n s x i j = BirdDet.get n (gridMatrixZ n s x).toArray i j := by
  rw [BirdDet.get_eq, ← rowInput_eq n s x, Array.getD_eq_getD_getElem?]
  by_cases h : n*i+j < n*n
  · simp only [readGrid, rowInput, Array.getElem?_ofFn, ite_eq_left h, dif_pos h,
      Option.getD_some, gridMatrixZ, Matrix.of_apply, Fin.divNat, Fin.modNat]
  · simp only [readGrid, rowInput, Array.getElem?_ofFn, ite_eq_right h, dif_neg h, Option.getD_none]

private theorem detGrid_eq (n s x : ℕ) :
    detDown n (readGrid n s x) = gridDetZ n s x := by
  have read : readGrid n s x = BirdDet.get n (gridMatrixZ n s x).toArray := by
    funext i j
    exact readGrid_eq n s x i j
  change detDown n (readGrid n s x) = BirdDet.birdDet n (gridMatrixZ n s x).toArray
  rw [read, detDown_eq]

end DetGridReplayCountdown

private theorem grid6_0 (x : Fin 7) :
    publishedTemplate6.valueZ 0 x.val = gridDetZ 6 0 x.val := by
  rewrite [← DetGridReplayCountdown.detGrid_eq]
  unfold SparseDetTemplate.valueZ
  fin_cases x <;> decide +kernel

private theorem grid6_1 (x : Fin 7) :
    publishedTemplate6.valueZ 1 x.val = gridDetZ 6 1 x.val := by
  rewrite [← DetGridReplayCountdown.detGrid_eq]
  unfold SparseDetTemplate.valueZ
  fin_cases x <;> decide +kernel

private theorem grid6_2 (x : Fin 7) :
    publishedTemplate6.valueZ 2 x.val = gridDetZ 6 2 x.val := by
  rewrite [← DetGridReplayCountdown.detGrid_eq]
  unfold SparseDetTemplate.valueZ
  fin_cases x <;> decide +kernel

private theorem grid6_3 (x : Fin 7) :
    publishedTemplate6.valueZ 3 x.val = gridDetZ 6 3 x.val := by
  rewrite [← DetGridReplayCountdown.detGrid_eq]
  unfold SparseDetTemplate.valueZ
  fin_cases x <;> decide +kernel

private theorem grid6_4 (x : Fin 7) :
    publishedTemplate6.valueZ 4 x.val = gridDetZ 6 4 x.val := by
  rewrite [← DetGridReplayCountdown.detGrid_eq]
  unfold SparseDetTemplate.valueZ
  fin_cases x <;> decide +kernel

private theorem grid6_5 (x : Fin 7) :
    publishedTemplate6.valueZ 5 x.val = gridDetZ 6 5 x.val := by
  rewrite [← DetGridReplayCountdown.detGrid_eq]
  unfold SparseDetTemplate.valueZ
  fin_cases x <;> decide +kernel

private theorem grid6_6 (x : Fin 7) :
    publishedTemplate6.valueZ 6 x.val = gridDetZ 6 6 x.val := by
  rewrite [← DetGridReplayCountdown.detGrid_eq]
  unfold SparseDetTemplate.valueZ
  fin_cases x <;> decide +kernel

private theorem grid6 (s x : Fin 7) :
    publishedTemplate6.valueZ s.val x.val = gridDetZ 6 s.val x.val := by
  fin_cases s
  · exact grid6_0 x
  · exact grid6_1 x
  · exact grid6_2 x
  · exact grid6_3 x
  · exact grid6_4 x
  · exact grid6_5 x
  · exact grid6_6 x

theorem publishedGrid6 : SparseDetGrid 6 publishedTemplate6 := by
  intro s x
  have eq := congrArg (fun z : ℤ => (z:ℚ)) (grid6 s x)
  simpa only [publishedTemplate6.valueZ_cast,gridDetZ_cast (by decide : 6 ≤ 7)] using eq

private theorem grid7_0 (x : Fin 8) :
    publishedTemplate7.valueZ 0 x.val = gridDetZ 7 0 x.val := by
  rewrite [← DetGridReplayCountdown.detGrid_eq]
  unfold SparseDetTemplate.valueZ
  fin_cases x <;> decide +kernel

private theorem grid7_1 (x : Fin 8) :
    publishedTemplate7.valueZ 1 x.val = gridDetZ 7 1 x.val := by
  rewrite [← DetGridReplayCountdown.detGrid_eq]
  unfold SparseDetTemplate.valueZ
  fin_cases x <;> decide +kernel

private theorem grid7_2 (x : Fin 8) :
    publishedTemplate7.valueZ 2 x.val = gridDetZ 7 2 x.val := by
  rewrite [← DetGridReplayCountdown.detGrid_eq]
  unfold SparseDetTemplate.valueZ
  fin_cases x <;> decide +kernel

private theorem grid7_3 (x : Fin 8) :
    publishedTemplate7.valueZ 3 x.val = gridDetZ 7 3 x.val := by
  rewrite [← DetGridReplayCountdown.detGrid_eq]
  unfold SparseDetTemplate.valueZ
  fin_cases x <;> decide +kernel

private theorem grid7_4 (x : Fin 8) :
    publishedTemplate7.valueZ 4 x.val = gridDetZ 7 4 x.val := by
  rewrite [← DetGridReplayCountdown.detGrid_eq]
  unfold SparseDetTemplate.valueZ
  fin_cases x <;> decide +kernel

private theorem grid7_5 (x : Fin 8) :
    publishedTemplate7.valueZ 5 x.val = gridDetZ 7 5 x.val := by
  rewrite [← DetGridReplayCountdown.detGrid_eq]
  unfold SparseDetTemplate.valueZ
  fin_cases x <;> decide +kernel

private theorem grid7_6 (x : Fin 8) :
    publishedTemplate7.valueZ 6 x.val = gridDetZ 7 6 x.val := by
  rewrite [← DetGridReplayCountdown.detGrid_eq]
  unfold SparseDetTemplate.valueZ
  fin_cases x <;> decide +kernel

private theorem grid7_7 (x : Fin 8) :
    publishedTemplate7.valueZ 7 x.val = gridDetZ 7 7 x.val := by
  rewrite [← DetGridReplayCountdown.detGrid_eq]
  unfold SparseDetTemplate.valueZ
  fin_cases x <;> decide +kernel

private theorem grid7 (s x : Fin 8) :
    publishedTemplate7.valueZ s.val x.val = gridDetZ 7 s.val x.val := by
  fin_cases s
  · exact grid7_0 x
  · exact grid7_1 x
  · exact grid7_2 x
  · exact grid7_3 x
  · exact grid7_4 x
  · exact grid7_5 x
  · exact grid7_6 x
  · exact grid7_7 x

theorem publishedGrid7 : SparseDetGrid 7 publishedTemplate7 := by
  intro s x
  have eq := congrArg (fun z : ℤ => (z:ℚ)) (grid7 s x)
  simpa only [publishedTemplate7.valueZ_cast,gridDetZ_cast (by decide : 7 ≤ 7)] using eq

end RKCert.ReviewedNative.ThreeInteriorPencil
