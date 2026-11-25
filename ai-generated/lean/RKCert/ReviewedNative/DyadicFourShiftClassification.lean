module

public import RKCert.ReviewedNative.PrimitiveDyadicNodal
public import RKCert.ReviewedNative.DyadicFourShiftRows

import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Exact small parity classification and the seventeen one-term exclusions -/

namespace RKResearch.Certified.DyadicFourShift

open scoped BigOperators
open RKResearch.Certified.RationalPrimeCut

abbrev DyadicParityAt (t u : ℕ) (j : Fin 4) : Prop :=
  dyadicParity t u (15-j.val) = 0 ∧
  (2 ≤ dyadicCredit t u (15-j.val) → dyadicParity t u (7-j.val) = 0)

abbrev DyadicParityGate (t u : ℕ) : Prop :=
  u ≤ t ∧ t-u ≤ u ∧
  DyadicParityAt t u 0 ∧ DyadicParityAt t u 1 ∧ DyadicParityAt t u 2 ∧ DyadicParityAt t u 3

def dyadicSurvivingPairs : List (ℕ × ℕ) :=
  [(0,0), (1,1), (2,1), (2,2), (3,2), (3,3), (8,8), (9,8), (9,9),
   (10,8), (10,9), (10,10), (11,8), (11,9), (11,10), (11,11), (16,8), (16,16)]

private theorem dyadicParityRow0 (u : Fin 17) :
    DyadicParityGate 0 u.val ↔ (0,u.val) ∈ dyadicSurvivingPairs := by
  fin_cases u <;> decide

private theorem dyadicParityRow1 (u : Fin 17) :
    DyadicParityGate 1 u.val ↔ (1,u.val) ∈ dyadicSurvivingPairs := by
  fin_cases u <;> decide

private theorem dyadicParityRow2 (u : Fin 17) :
    DyadicParityGate 2 u.val ↔ (2,u.val) ∈ dyadicSurvivingPairs := by
  fin_cases u <;> decide

private theorem dyadicParityRow3 (u : Fin 17) :
    DyadicParityGate 3 u.val ↔ (3,u.val) ∈ dyadicSurvivingPairs := by
  fin_cases u <;> decide

private theorem dyadicParityRow4 (u : Fin 17) :
    DyadicParityGate 4 u.val ↔ (4,u.val) ∈ dyadicSurvivingPairs := by
  fin_cases u <;> decide

private theorem dyadicParityRow5 (u : Fin 17) :
    DyadicParityGate 5 u.val ↔ (5,u.val) ∈ dyadicSurvivingPairs := by
  fin_cases u <;> decide

private theorem dyadicParityRow6 (u : Fin 17) :
    DyadicParityGate 6 u.val ↔ (6,u.val) ∈ dyadicSurvivingPairs := by
  fin_cases u <;> decide

private theorem dyadicParityRow7 (u : Fin 17) :
    DyadicParityGate 7 u.val ↔ (7,u.val) ∈ dyadicSurvivingPairs := by
  fin_cases u <;> decide

private theorem dyadicParityRow8 (u : Fin 17) :
    DyadicParityGate 8 u.val ↔ (8,u.val) ∈ dyadicSurvivingPairs := by
  fin_cases u <;> decide

private theorem dyadicParityRow9 (u : Fin 17) :
    DyadicParityGate 9 u.val ↔ (9,u.val) ∈ dyadicSurvivingPairs := by
  fin_cases u <;> decide

private theorem dyadicParityRow10 (u : Fin 17) :
    DyadicParityGate 10 u.val ↔ (10,u.val) ∈ dyadicSurvivingPairs := by
  fin_cases u <;> decide

private theorem dyadicParityRow11 (u : Fin 17) :
    DyadicParityGate 11 u.val ↔ (11,u.val) ∈ dyadicSurvivingPairs := by
  fin_cases u <;> decide

private theorem dyadicParityRow12 (u : Fin 17) :
    DyadicParityGate 12 u.val ↔ (12,u.val) ∈ dyadicSurvivingPairs := by
  fin_cases u <;> decide

private theorem dyadicParityRow13 (u : Fin 17) :
    DyadicParityGate 13 u.val ↔ (13,u.val) ∈ dyadicSurvivingPairs := by
  fin_cases u <;> decide

private theorem dyadicParityRow14 (u : Fin 17) :
    DyadicParityGate 14 u.val ↔ (14,u.val) ∈ dyadicSurvivingPairs := by
  fin_cases u <;> decide

private theorem dyadicParityRow15 (u : Fin 17) :
    DyadicParityGate 15 u.val ↔ (15,u.val) ∈ dyadicSurvivingPairs := by
  fin_cases u <;> decide

private theorem dyadicParityRow16 (u : Fin 17) :
    DyadicParityGate 16 u.val ↔ (16,u.val) ∈ dyadicSurvivingPairs := by
  fin_cases u <;> decide

theorem dyadicParityGate_exact (t u : Fin 17) :
    DyadicParityGate t.val u.val ↔ (t.val,u.val) ∈ dyadicSurvivingPairs := by
  fin_cases t
  · exact dyadicParityRow0 u
  · exact dyadicParityRow1 u
  · exact dyadicParityRow2 u
  · exact dyadicParityRow3 u
  · exact dyadicParityRow4 u
  · exact dyadicParityRow5 u
  · exact dyadicParityRow6 u
  · exact dyadicParityRow7 u
  · exact dyadicParityRow8 u
  · exact dyadicParityRow9 u
  · exact dyadicParityRow10 u
  · exact dyadicParityRow11 u
  · exact dyadicParityRow12 u
  · exact dyadicParityRow13 u
  · exact dyadicParityRow14 u
  · exact dyadicParityRow15 u
  · exact dyadicParityRow16 u

private theorem nat_parity_eq_zero {s : ℕ} (hs : s < 2) (h : (s : ZMod 2) = 0) :
    s = 0 := by
  have hh := congrArg ZMod.val h
  simpa only [ZMod.val_natCast, ZMod.val_zero, Nat.mod_eq_of_lt hs] using hh

theorem cast_zero_four_of_credit {a : ℤ} {n : ℕ} (hn : 2 ≤ n) (h : (2 : ℤ)^n ∣ a) :
    (a : ZMod 4) = 0 := by
  have h4 : (4 : ℤ) ∣ (2 : ℤ)^n := pow_dvd_pow (2 : ℤ) hn
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd a 4).mpr (h4.trans h)

theorem dyadicParityGate_of_paid (a : ℕ → ℤ) {t u : ℕ} (hu : u ≤ t) (hor : t-u ≤ u)
    (parity : ∀ k, (a k : ZMod 2) = (dyadicParity t u k : ZMod 2))
    (divs : ∀ k, (2 : ℤ)^(dyadicCredit t u k) ∣ a k)
    (paid : DyadicFourRows8 a) : DyadicParityGate t u := by
  have test (j : Fin 4) : DyadicParityAt t u j := by
    refine ⟨?_,?_⟩
    · apply nat_parity_eq_zero (dyadicParity_lt_two _ _ _)
      rw [← parity]
      exact dyadicPaid2 a paid j
    · intro h
      have z := dyadicPaid4 a paid j
      rw [cast_zero_four_of_credit h (divs _), zero_add] at z
      apply nat_parity_eq_zero (dyadicParity_lt_two _ _ _)
      rw [← parity]
      exact dyadic_even_of_twice_zero_four z
  exact ⟨hu,hor,test 0,test 1,test 2,test 3⟩

def dyadicPickShift (t u : ℕ) : Fin 4 :=
  ⟨(if t ≤ 3 then 3-t else if t < 11 then 11-t
    else if (t,u) = (11,8) then 1 else if t=16 then 3 else 0)%4,
      Nat.mod_lt _ (by decide)⟩

def dyadicPickTerm (t u : ℕ) : ℕ := if (t,u) = (11,8) then 10 else t

abbrev DyadicOneTerm (t u : ℕ) (j : Fin 4) (i : ℕ) : Prop :=
  i < 20 ∧ dyadicWeight j i = 4 ∧ dyadicParity t u i = 1 ∧
    ∀ k : Fin 20, k.val ≠ i → (dyadicWeight j k.val * 2^(dyadicCredit t u k.val))%8 = 0

theorem dyadicSurvivingPairs_test (s : ℕ × ℕ) (h : s ∈ dyadicSurvivingPairs) :
    s = (16,8) ∨ DyadicOneTerm s.1 s.2 (dyadicPickShift s.1 s.2) (dyadicPickTerm s.1 s.2) := by
  simp only [dyadicSurvivingPairs, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst s <;> decide

private theorem four_times_odd_eight {a : ℤ} (h : (a : ZMod 2) = 1) :
    (4 : ZMod 8)*(a : ZMod 8) = 4 := by
  have hd : (2 : ℤ) ∣ a-1 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (a-1) 2).mp
      (by simp only [Int.cast_sub, Int.cast_one, h, sub_self])
  obtain ⟨v,hv⟩ := hd
  have ha : a = 2*v+1 := by omega
  have h42 : (4 : ZMod 8)*2 = 0 := by
    change ((4 : ℕ) : ZMod 8)*((2 : ℕ) : ZMod 8) = 0
    rw [← Nat.cast_mul]
    exact ZMod.natCast_self 8
  rw [ha, Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_one, mul_add, ← mul_assoc,
    h42, zero_mul, zero_add, mul_one]

theorem dyadicOneTerm_excludes_paid (a : ℕ → ℤ) {t u : ℕ} {j : Fin 4} {i : ℕ}
    (parity : ∀ k, (a k : ZMod 2) = (dyadicParity t u k : ZMod 2))
    (divs : ∀ k, (2 : ℤ)^(dyadicCredit t u k) ∣ a k)
    (paid : DyadicFourRows8 a) (test : DyadicOneTerm t u j i) : False := by
  rcases test with ⟨hi,hw,hp,test⟩
  have vanish (k : ℕ) (hk : k ∈ Finset.range 20) (hki : k ≠ i) :
      (dyadicWeight j k : ZMod 8)*(a k : ZMod 8) = 0 := by
    have m := test ⟨k,Finset.mem_range.mp hk⟩ hki
    have zr : ((dyadicWeight j k*2^(dyadicCredit t u k) : ℕ) : ZMod 8) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr (Nat.dvd_of_mod_eq_zero m)
    obtain ⟨z,hz⟩ := divs k
    calc
      _ = ((dyadicWeight j k*2^(dyadicCredit t u k) : ℕ) : ZMod 8)*(z : ZMod 8) := by
        rw [hz, Int.cast_mul, Int.cast_pow, Int.cast_ofNat, Nat.cast_mul, Nat.cast_pow,
          Nat.cast_ofNat, mul_assoc]
      _ = _ := by rw [zr,zero_mul]
  have h1 : (a i : ZMod 2) = 1 := by rw [parity, hp, Nat.cast_one]
  have sumEq : (∑ k ∈ Finset.range 20, (dyadicWeight j k : ZMod 8)*(a k : ZMod 8)) =
      (dyadicWeight j i : ZMod 8)*(a i : ZMod 8) :=
    Finset.sum_eq_single i vanish (fun h => (h (Finset.mem_range.mpr hi)).elim)
  have z := paid j
  rw [sumEq, hw, Nat.cast_ofNat, four_times_odd_eight h1] at z
  have e := congrArg ZMod.val z
  change 4 = 0 at e
  omega

end RKResearch.Certified.DyadicFourShift
