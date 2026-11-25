module

public import RKCert.ReviewedNative.ReducedHilbertMomentPrimeCut

import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Four exact paid shifts, with all arithmetic on natural residues -/

namespace RKResearch.Certified.DyadicFourShift

open RKResearch.Certified.RationalPrimeCut
open scoped BigOperators

def dyadicScale : ℕ := 232792560

def dyadicWeight (j : Fin 4) (k : ℕ) : ℕ :=
  (if k=15-j.val then 1 else 0) +
  (if k=7-j.val then 2 else 0) +
  (if k=3-j.val then 4 else 0) +
  (if k=11-j.val then 4 else 0) +
  (if k=19-j.val then 4 else 0)

def DyadicFourRows8 (a : ℕ → ℤ) : Prop :=
  ∀ j : Fin 4, (∑ k ∈ Finset.range 20, (dyadicWeight j k : ZMod 8)*(a k : ZMod 8)) = 0

theorem divisor_dyadicScale (d : ℕ) (hp : 0 < d) (ht : d ≤ 20) : d ∣ dyadicScale := by
  interval_cases d <;> decide

theorem dyadicWeight_nat_formula (j : Fin 4) (k : ℕ) (hk : k ≤ 16) :
    (7 * (dyadicScale/(k+j.val+1))) % 8 = dyadicWeight j k := by
  fin_cases j <;> interval_cases k <;> decide

private theorem dyadicWeight_cast (j : Fin 4) (k : ℕ) (hk : k ≤ 16) :
    ((7 * (dyadicScale/(k+j.val+1)) : ℕ) : ZMod 8) = (dyadicWeight j k : ZMod 8) := by
  rw [← dyadicWeight_nat_formula j k hk, ZMod.natCast_mod]

private theorem cast_dyadicScale_div (d : ℕ) (hp : 0 < d) (ht : d ≤ 20) :
    (dyadicScale : ℚ) / (d : ℚ) = ((dyadicScale/d : ℕ) : ℚ) := by
  apply (div_eq_iff (Nat.cast_ne_zero.mpr hp.ne')).mpr
  rw [← Nat.cast_mul, Nat.div_mul_cancel (divisor_dyadicScale d hp ht)]

theorem clear_uniformIntRow_dyadicScale (a : ℕ → ℤ) (m : ℕ) (hm : m ≤ 16)
    (j : Fin 4) (h : UniformIntRowZero a m j.val) :
    (∑ k ∈ Finset.range (m+1), (dyadicScale/(k+j.val+1) : ℕ) * a k) = (0 : ℤ) := by
  have hj := j.isLt
  apply Int.cast_injective (α := ℚ)
  change ((∑ k ∈ Finset.range (m+1), (dyadicScale/(k+j.val+1) : ℕ) * a k : ℤ) : ℚ) = 0
  calc
    _ = ∑ k ∈ Finset.range (m+1), ((dyadicScale/(k+j.val+1) : ℕ) : ℚ) * (a k : ℚ) := by
      simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast]
    _ = (dyadicScale : ℚ) * ∑ k ∈ Finset.range (m+1), (a k : ℚ) / ((k+j.val+1 : ℕ) : ℚ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hh := Finset.mem_range.mp hk
      rw [← cast_dyadicScale_div (k+j.val+1) (by omega) (by omega)]
      rw [div_eq_mul_inv, div_eq_mul_inv]
      ring
    _ = _ := by rw [show (∑ k ∈ Finset.range (m+1), (a k : ℚ) /
        ((k+j.val+1 : ℕ) : ℚ)) = 0 from h, mul_zero]

theorem dyadicFourRows8_of_uniformInt (a : ℕ → ℤ) {m : ℕ} (hm : m ≤ 16)
    (tail : ∀ k, m < k → a k = 0) (rows : ∀ j : Fin 4, UniformIntRowZero a m j.val) :
    DyadicFourRows8 a := by
  intro j
  have cleared := clear_uniformIntRow_dyadicScale a m hm j (rows j)
  have scaled := congrArg (Int.castRingHom (ZMod 8)) cleared
  have hs : (∑ k ∈ Finset.range (m+1),
      ((dyadicScale/(k+j.val+1) : ℕ) : ZMod 8)*(a k : ZMod 8)) = 0 := by
    simpa only [map_sum, map_mul, map_zero, Int.coe_castRingHom, Int.cast_natCast] using scaled
  have sum20 :
      (∑ k ∈ Finset.range (m+1), (dyadicWeight j k : ZMod 8)*(a k : ZMod 8)) =
        ∑ k ∈ Finset.range 20, (dyadicWeight j k : ZMod 8)*(a k : ZMod 8) := by
    apply Finset.sum_subset
    · exact Finset.range_subset_range.mpr (by omega)
    · intro k _ hk
      have hkm : ¬ k < m+1 := by simpa only [Finset.mem_range] using hk
      rw [tail k (by omega), Int.cast_zero, mul_zero]
  rw [← sum20]
  calc
    _ = ∑ k ∈ Finset.range (m+1),
        (7 : ZMod 8)*(((dyadicScale/(k+j.val+1) : ℕ) : ZMod 8)*(a k : ZMod 8)) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hi := Finset.mem_range.mp hk
      rw [← dyadicWeight_cast j k (by omega), Nat.cast_mul, mul_assoc]
      simp only [Nat.cast_ofNat]
    _ = _ := by rw [← Finset.mul_sum, hs, mul_zero]

private theorem sum_indicator_piece (a : ℕ → ZMod 8) (c i : ℕ) (hi : i < 20) :
    (∑ k ∈ Finset.range 20, ((if k=i then c else 0 : ℕ) : ZMod 8)*a k) =
      (c : ZMod 8)*a i := by
  simp only [apply_ite, Nat.cast_zero, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_range, hi, if_true]

theorem dyadicFiveTerms8 (a : ℕ → ℤ) (h : DyadicFourRows8 a) (j : Fin 4) :
    (a (15-j.val) : ZMod 8) + 2*(a (7-j.val) : ZMod 8) +
      4*(a (3-j.val) : ZMod 8) + 4*(a (11-j.val) : ZMod 8) +
      4*(a (19-j.val) : ZMod 8) = 0 := by
  have hj := j.isLt
  have hs := h j
  simp only [dyadicWeight, Nat.cast_add, add_mul, Finset.sum_add_distrib] at hs
  rw [sum_indicator_piece _ 1 _ (by omega), sum_indicator_piece _ 2 _ (by omega),
    sum_indicator_piece _ 4 (3-j.val) (by omega),
    sum_indicator_piece _ 4 (11-j.val) (by omega),
    sum_indicator_piece _ 4 (19-j.val) (by omega)] at hs
  simpa only [Nat.cast_one, Nat.cast_ofNat, one_mul] using hs

def dyadicReduce8to2 : ZMod 8 →+* ZMod 2 := ZMod.castHom (by decide : 2 ∣ 8) (ZMod 2)
def dyadicReduce8to4 : ZMod 8 →+* ZMod 4 := ZMod.castHom (by decide : 4 ∣ 8) (ZMod 4)
def dyadicReduce4to2 : ZMod 4 →+* ZMod 2 := ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)

theorem dyadicTwo_zero : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
theorem dyadicFour_zero_two : (4 : ZMod 2) = 0 := by
  change ((4 : ℕ) : ZMod 2) = 0
  rw [← ZMod.natCast_mod 4 2]
  rfl
theorem dyadicFour_zero_four : (4 : ZMod 4) = 0 := ZMod.natCast_self 4

theorem dyadicPaid2 (a : ℕ → ℤ) (h : DyadicFourRows8 a) (j : Fin 4) :
    (a (15-j.val) : ZMod 2) = 0 := by
  have z := congrArg dyadicReduce8to2 (dyadicFiveTerms8 a h j)
  simpa only [map_add, map_mul, map_intCast, map_ofNat, map_zero,
    dyadicTwo_zero, dyadicFour_zero_two, zero_mul, add_zero] using z

theorem dyadicPaid4 (a : ℕ → ℤ) (h : DyadicFourRows8 a) (j : Fin 4) :
    (a (15-j.val) : ZMod 4) + 2*(a (7-j.val) : ZMod 4) = 0 := by
  have z := congrArg dyadicReduce8to4 (dyadicFiveTerms8 a h j)
  simpa only [map_add, map_mul, map_intCast, map_ofNat, map_zero,
    dyadicFour_zero_four, zero_mul, add_zero] using z

theorem dyadic_even_of_twice_zero_four {a : ℤ} (h : (2 : ZMod 4)*(a : ZMod 4) = 0) :
    (a : ZMod 2) = 0 := by
  have hd : (4 : ℤ) ∣ 2*a :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (2*a) 4).mp (by simpa only [Int.cast_mul, Int.cast_ofNat] using h)
  have hd' : (2 : ℤ)*2 ∣ 2*a := by simpa using hd
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd a 2).mpr
    ((mul_dvd_mul_iff_left (by decide : (2 : ℤ) ≠ 0)).mp hd')

end RKResearch.Certified.DyadicFourShift
