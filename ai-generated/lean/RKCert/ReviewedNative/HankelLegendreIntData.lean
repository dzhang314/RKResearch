module

public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.List.Basic
public import Mathlib.Data.Nat.Factorial.Basic

@[expose] public section

/-! # Primitive integer Legendre data, paid through order twenty

These are rational-polynomial numerators with natural paid denominators.
All certified decisions below use kernel reduction. The field transport
must use invertible primes ≤19, never an assumed global ℚ → K map. -/
namespace RKResearch.Certified.Graded.HankelLegendreIntData

structure ScaledRow where
  denominator : ℕ
  numerator : List ℤ

def paidNat : ℕ := 2432902008176640000

theorem paidNat_eq_factorial : paidNat = Nat.factorial 20 := by decide +kernel

def modeRows : List ScaledRow :=
  [⟨1, [1]⟩,
   ⟨1, [0, 1]⟩,
   ⟨3, [-1, 0, 3]⟩,
   ⟨5, [0, -3, 0, 5]⟩,
   ⟨35, [3, 0, -30, 0, 35]⟩,
   ⟨63, [0, 15, 0, -70, 0, 63]⟩,
   ⟨231, [-5, 0, 105, 0, -315, 0, 231]⟩,
   ⟨429, [0, -35, 0, 315, 0, -693, 0, 429]⟩,
   ⟨6435, [35, 0, -1260, 0, 6930, 0, -12012, 0, 6435]⟩,
   ⟨12155, [0, 315, 0, -4620, 0, 18018, 0, -25740, 0, 12155]⟩,
   ⟨46189, [-63, 0, 3465, 0, -30030, 0, 90090, 0, -109395, 0, 46189]⟩]

def tail5Rows : List ScaledRow :=
  [⟨1, [1]⟩,
   ⟨1, [0, 1]⟩,
   ⟨99, [-25, 0, 99]⟩,
   ⟨117, [0, -59, 0, 117]⟩,
   ⟨19305, [1225, 0, -14586, 0, 19305]⟩,
   ⟨8415, [0, 1599, 0, -8470, 0, 8415]⟩,
   ⟨415701, [-6615, 0, 157755, 0, -522665, 0, 415701]⟩]

def tail6Rows : List ScaledRow :=
  [⟨1, [1]⟩,
   ⟨1, [0, 1]⟩,
   ⟨143, [-36, 0, 143]⟩,
   ⟨165, [0, -83, 0, 165]⟩,
   ⟨12155, [768, 0, -9165, 0, 12155]⟩,
   ⟨46189, [0, 8745, 0, -46410, 0, 46189]⟩]

def tail7Rows : List ScaledRow :=
  [⟨1, [1]⟩,
   ⟨1, [0, 1]⟩,
   ⟨195, [-49, 0, 195]⟩,
   ⟨221, [0, -111, 0, 221]⟩,
   ⟨20995, [1323, 0, -15810, 0, 20995]⟩]

def defaultRow : ScaledRow := ⟨1,[1]⟩

def modeRow (n : ℕ) : ScaledRow := modeRows[n]?.getD defaultRow

def tailRow (a n : ℕ) : ScaledRow :=
  (if a=5 then tail5Rows else if a=6 then tail6Rows else if a=7 then tail7Rows else [])[n]?.getD defaultRow

def coeffInt (r : ScaledRow) (j : ℕ) : ℤ := r.numerator[j]?.getD 0

def atom (k : ℕ) : ℤ := if k%2=0 then (paidNat/(k+1) : ℕ) else 0

def intPaidTest : List ℤ → ℕ → ℤ
  | [], _ => 0
  | c::cs, j => c * atom j + intPaidTest cs (j+1)

theorem paid_atom_denominators : ∀ j : Fin 20, j.val+1 ∣ paidNat := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem mode_bands : ∀ n : Fin 11,
    (modeRow n.val).denominator ∣ paidNat ∧
    (modeRow n.val).numerator.length = n.val+1 ∧
    coeffInt (modeRow n.val) n.val = ((modeRow n.val).denominator : ℤ) ∧
    ∀ i : Fin (n.val+1), i.val%2 ≠ n.val%2 → coeffInt (modeRow n.val) i.val = 0 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem mode_tests : ∀ n : Fin 11, ∀ j : Fin n.val,
    intPaidTest (modeRow n.val).numerator j.val = 0 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem mode_norm_num : ∀ n : Fin 10,
    0 < intPaidTest (modeRow n.val).numerator n.val ∧
    (intPaidTest (modeRow n.val).numerator n.val).natAbs ∣ paidNat^2 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem tail_denominators :
    (∀ n : Fin 7, (tailRow 5 n.val).denominator ∣ paidNat^2) ∧
    (∀ n : Fin 6, (tailRow 6 n.val).denominator ∣ paidNat^2) ∧
    (∀ n : Fin 5, (tailRow 7 n.val).denominator ∣ paidNat^2) := by
  decide +kernel

/-- Coefficient of A = X*B − β_i*C, with the three row denominators
and β's paid denominator multiplied through. -/
abbrev ClearedRecurrence (A B C : ScaledRow) (i j : ℕ) : Prop :=
  let betaDen : ℤ := ((2*i-1)*(2*i+1) : ℕ)
  let betaNum : ℤ := (i*i : ℕ)
  let shifted := if j=0 then 0 else coeffInt B (j-1)
  coeffInt A j * B.denominator * C.denominator * betaDen =
    shifted * A.denominator * C.denominator * betaDen -
      betaNum * coeffInt C j * A.denominator * B.denominator

set_option maxRecDepth 4096 in
theorem mode_recurrence : ∀ n : Fin 9, ∀ j : Fin (n.val+3),
    ClearedRecurrence (modeRow (n.val+2)) (modeRow (n.val+1)) (modeRow n.val)
      (n.val+1) j.val := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem tail_recurrence :
    (∀ n : Fin 5, ∀ j : Fin (n.val+3),
      ClearedRecurrence (tailRow 5 (n.val+2)) (tailRow 5 (n.val+1)) (tailRow 5 n.val) (5+n.val) j.val) ∧
    (∀ n : Fin 4, ∀ j : Fin (n.val+3),
      ClearedRecurrence (tailRow 6 (n.val+2)) (tailRow 6 (n.val+1)) (tailRow 6 n.val) (6+n.val) j.val) ∧
    (∀ n : Fin 3, ∀ j : Fin (n.val+3),
      ClearedRecurrence (tailRow 7 (n.val+2)) (tailRow 7 (n.val+1)) (tailRow 7 n.val) (7+n.val) j.val) := by
  decide +kernel

/-- The two sensitive rows need two equations each; no large paid
prime can simultaneously kill the two displayed numerators. -/
theorem row9i_bezout : (3004 : ℤ)*6432 + (-575 : ℤ)*33603 = 3 := by
  decide +kernel

theorem row9ii_bezout : ((-3879) : ℤ)*(-796) + (-40 : ℤ)*77192 = 4 := by
  decide +kernel

end RKResearch.Certified.Graded.HankelLegendreIntData
