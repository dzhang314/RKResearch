module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic

@[expose] public section

/-! # A constant-term obstruction with factorial denominators

Over the rationals Mathlib's `padicValRat q 0` is zero, not infinity.
Every strict valuation hypothesis below is on *nonzero* terms. This
keeps the finite-sum argument valid when terms or partial sums vanish. -/

namespace RKResearch.Certified

open scoped BigOperators

/-- At an odd prime the factorial denominator loses strictly fewer than
`j` prime factors whenever `j` is positive. -/
theorem factorial_succ_multiplicity_lt_of_two_lt
    {q j : ℕ} [Fact q.Prime] (hq : 2 < q) (hj : 0 < j) :
    multiplicity q ((j + 1).factorial) < j := by
  have hscale : 2 ≤ q - 1 := by omega
  have hle := Nat.mul_le_mul_right (multiplicity q ((j + 1).factorial)) hscale
  have hLegendre := sub_one_mul_multiplicity_factorial_lt_of_ne_zero q
    (n := j + 1) (Nat.succ_ne_zero j)
  have h := hle.trans_lt hLegendre
  omega

/-- Any nonzero integer multiple of a prime has rational valuation at least one. -/
theorem one_le_padicValRat_intCast_of_dvd {q : ℕ} [Fact q.Prime] {x : ℤ}
    (hx : x ≠ 0) (hq : (q : ℤ) ∣ x) : 1 ≤ padicValRat q (x : ℚ) := by
  rw [padicValRat.of_int, padicValInt]
  have h : 1 ≤ multiplicity q x.natAbs :=
    one_le_multiplicity_of_dvd (Int.natAbs_ne_zero.mpr hx) (Int.ofNat_dvd_left.mp hq)
  exact_mod_cast h

/-- With an integral multiplier, a nonzero term `a*x^j/d` has positive
valuation if `q ∣ x` and fewer than `j` powers of `q` divide `d`. -/
theorem padicValRat_pos_of_dvd_power_div_nat {q j d : ℕ} [Fact q.Prime]
    {x a : ℤ} (hx : (q : ℤ) ∣ x) (hd : multiplicity q d < j)
    (ht : (a : ℚ) * (x : ℚ) ^ j / (d : ℚ) ≠ 0) :
    0 < padicValRat q ((a : ℚ) * (x : ℚ) ^ j / (d : ℚ)) := by
  have hN : (a : ℚ) * (x : ℚ) ^ j ≠ 0 := fun h => ht (by rw [h, zero_div])
  have hD : (d : ℚ) ≠ 0 := fun h => ht (by rw [h, div_zero])
  obtain ⟨hA, hPow⟩ := mul_ne_zero_iff.mp hN
  have hj : j ≠ 0 := Nat.ne_of_gt ((Nat.zero_le _).trans_lt hd)
  have hx' : x ≠ 0 := by
    intro h
    exact hPow (by simp only [h, Int.cast_zero, zero_pow hj])
  have hX := one_le_padicValRat_intCast_of_dvd hx' hx
  have hA0 : 0 ≤ padicValRat q (a : ℚ) := by
    rw [padicValRat.of_int]
    exact Int.natCast_nonneg _
  rw [padicValRat.div hN hD, padicValRat.mul hA hPow, padicValRat.pow, padicValRat.of_nat]
  have hExp := mul_le_mul_of_nonneg_left hX (Int.natCast_nonneg j)
  rw [mul_one] at hExp
  have hd' : (multiplicity q d : ℤ) < (j : ℤ) := by exact_mod_cast hd
  omega

/-- A nonzero finite sum inherits a strict valuation lower bound on its
nonzero summands. No noncancellation hypothesis on its partial sums. -/
theorem lt_padicValRat_finsetSum_of_ne_zero {ι : Type*} {q : ℕ} [Fact q.Prime]
    (S : Finset ι) (f : ι → ℚ) {v : ℤ}
    (h : ∀ i ∈ S, f i ≠ 0 → v < padicValRat q (f i))
    (hSum : (∑ i ∈ S, f i) ≠ 0) :
    v < padicValRat q (∑ i ∈ S, f i) := by
  classical
  revert h hSum
  induction S using Finset.induction_on with
  | empty =>
    intro _ hSum
    exact (hSum (by simp)).elim
  | @insert i T hi ih =>
    intro h hSum
    rw [Finset.sum_insert hi] at hSum ⊢
    have hHead (hn : f i ≠ 0) : v < padicValRat q (f i) :=
      h i (Finset.mem_insert_self _ _) hn
    have hTail (hn : (∑ j ∈ T, f j) ≠ 0) :
        v < padicValRat q (∑ j ∈ T, f j) :=
      ih (fun j hj => h j (Finset.mem_insert_of_mem hj)) hn
    by_cases h0 : f i = 0
    · rw [h0, zero_add] at hSum ⊢
      exact hTail hSum
    by_cases ht : (∑ j ∈ T, f j) = 0
    · rw [ht, add_zero]
      exact hHead h0
    exact (lt_min (hHead h0) (hTail ht)).trans_le (padicValRat.min_le_padicValRat_add hSum)

/-- A single nonzero term of strictly smallest valuation cannot cancel
a finite sum of terms of larger valuation or zero terms. -/
theorem add_finsetSum_ne_zero_of_padicValRat_lt {ι : Type*} {q : ℕ} [Fact q.Prime]
    (S : Finset ι) (f : ι → ℚ) {c : ℚ} (hc : c ≠ 0)
    (h : ∀ i ∈ S, f i ≠ 0 → padicValRat q c < padicValRat q (f i)) :
    c + ∑ i ∈ S, f i ≠ 0 := by
  intro hz
  have he : (∑ i ∈ S, f i) = -c := eq_neg_of_add_eq_zero_right hz
  have hSum : (∑ i ∈ S, f i) ≠ 0 := by
    rw [he]
    exact neg_ne_zero.mpr hc
  have hlt := lt_padicValRat_finsetSum_of_ne_zero S f h hSum
  rw [he, padicValRat.neg] at hlt
  exact (lt_irrefl _) hlt

/-- Constant term one cannot be cancelled by higher powers of a
prime-divisible integer with denominators below their degree's prime budget. -/
theorem one_add_power_div_sum_ne_zero_of_dvd {q : ℕ} [Fact q.Prime]
    (S : Finset ℕ) (a : ℕ → ℤ) (d : ℕ → ℕ)
    {x : ℤ} (hx : (q : ℤ) ∣ x) (hd : ∀ j ∈ S, multiplicity q (d j) < j) :
    (1 + ∑ j ∈ S, (a j : ℚ) * (x : ℚ) ^ j / (d j : ℚ)) ≠ 0 := by
  apply add_finsetSum_ne_zero_of_padicValRat_lt (q := q) _ _ one_ne_zero
  intro j hj ht
  rw [padicValRat.one]
  exact padicValRat_pos_of_dvd_power_div_nat hx (hd j hj) ht

/-- Specialization to factorial denominators at an odd prime. -/
theorem one_add_factorial_power_sum_ne_zero_of_dvd {q : ℕ} [Fact q.Prime]
    (hq : 2 < q) (S : Finset ℕ) (hS : ∀ j ∈ S, 0 < j) (a : ℕ → ℤ)
    {x : ℤ} (hx : (q : ℤ) ∣ x) :
    (1 + ∑ j ∈ S, (a j : ℚ) * (x : ℚ) ^ j / ((j + 1).factorial : ℚ)) ≠ 0 :=
  one_add_power_div_sum_ne_zero_of_dvd S a (fun j => (j + 1).factorial) hx
    (fun j hj => factorial_succ_multiplicity_lt_of_two_lt hq (hS j hj))

end RKResearch.Certified
