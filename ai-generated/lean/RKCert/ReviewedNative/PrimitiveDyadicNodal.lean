module

public import RKCert.ReviewedNative.PrimeNodalFactorDegree

import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Rat.Lemmas
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Parity of a product of primitive rational nodal factors -/

namespace RKResearch.Certified.DyadicFourShift

open Polynomial RKResearch.Certified.RationalPrimeCut
open scoped BigOperators Polynomial Classical

abbrev denOdd (r : ℚ) : Prop := (r.den : ZMod 2) ≠ 0
abbrev numEven (r : ℚ) : Prop := (r.num : ZMod 2) = 0

noncomputable def dyadicDenCount (T : Finset ℚ) : ℕ := (T.filter denOdd).card
noncomputable def dyadicEvenCount (T : Finset ℚ) : ℕ := (T.filter numEven).card

def dyadicCredit (t u k : ℕ) : ℕ := max (u-k) (k-t)

theorem zmodTwo_choices (x : ZMod 2) : x = 0 ∨ x = 1 := by
  have hx := ZMod.val_lt x
  have h : x.val = 0 ∨ x.val = 1 := by omega
  rcases h with h | h
  · left
    rw [← ZMod.natCast_zmod_val x, h, Nat.cast_zero]
  · right
    rw [← ZMod.natCast_zmod_val x, h, Nat.cast_one]

theorem zmodTwo_neg_one : -(1 : ZMod 2) = 1 := by
  have h : (1 : ZMod 2) + 1 = 0 := by decide +kernel
  exact (eq_neg_of_add_eq_zero_left h).symm

theorem denOdd_of_numEven (r : ℚ) (hn : numEven r) : denOdd r := by
  intro h
  have hd : 2 ∣ r.den := (ZMod.natCast_eq_zero_iff r.den 2).mp h
  have hz : (2 : ℕ) ∣ r.num.natAbs :=
    Int.ofNat_dvd_left.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd r.num 2).mp hn)
  exact Nat.prime_two.ne_one ((Nat.gcd_eq_one_iff.mp r.reduced) 2 hz hd)

theorem dyadicEvenCount_le_denCount (T : Finset ℚ) : dyadicEvenCount T ≤ dyadicDenCount T := by
  apply Finset.card_le_card
  intro r hr
  exact Finset.mem_filter.mpr
    ⟨(Finset.mem_filter.mp hr).1, denOdd_of_numEven r (Finset.mem_filter.mp hr).2⟩

theorem dyadicDenCount_le_card (T : Finset ℚ) : dyadicDenCount T ≤ T.card :=
  Finset.card_le_card (Finset.filter_subset _ _)

theorem dyadicOddNumeratorDenCount (T : Finset ℚ) :
    (T.filter (fun r => denOdd r ∧ ¬ numEven r)).card = dyadicDenCount T - dyadicEvenCount T := by
  have h := Finset.card_filter_add_card_filter_not (s := T.filter denOdd) numEven
  have he : (T.filter denOdd).filter numEven = T.filter numEven := by
    ext r
    simp only [Finset.mem_filter]
    exact ⟨fun h => ⟨h.1.1,h.2⟩, fun h => ⟨⟨h.1,denOdd_of_numEven r h.2⟩,h.2⟩⟩
  rw [he, Finset.filter_filter] at h
  change dyadicEvenCount T + (T.filter (fun r => denOdd r ∧ ¬ numEven r)).card =
    dyadicDenCount T at h
  omega

/-- Constant-end version of the reviewed convolution budget. -/
theorem coeff_pow_lower_budget_mul {R : Type*} [CommSemiring R]
    (q : R) {P Q : R[X]} {u v : ℕ}
    (hP : ∀ k, q^(u-k) ∣ P.coeff k) (hQ : ∀ k, q^(v-k) ∣ Q.coeff k)
    (k : ℕ) : q^((u+v)-k) ∣ (P*Q).coeff k := by
  rw [Polynomial.coeff_mul]
  apply Finset.dvd_sum
  intro ij hij
  have hsum := Finset.mem_antidiagonal.mp hij
  refine (pow_dvd_pow q (show (u+v)-k ≤ (u-ij.1)+(v-ij.2) by omega)).trans ?_
  rw [pow_add]
  exact mul_dvd_mul (hP ij.1) (hQ ij.2)

theorem coeff_pow_lower_budget_prod_linear {R ι : Type*} [CommSemiring R]
    (q : R) (S : Finset ι) (a b : ι → R) (mark : ι → Prop) [DecidablePred mark]
    (hmark : ∀ i ∈ S, mark i → q ∣ b i) :
    ∀ k, q^((S.filter mark).card-k) ∣ (∏ i ∈ S, (C (a i)*X+C (b i) : R[X])).coeff k := by
  revert hmark
  induction S using Finset.induction_on with
  | empty =>
    intro _ k
    simp
  | @insert i S hi ih =>
    intro h k
    have small := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    have first (j : ℕ) :
        q^((if mark i then 1 else 0)-j) ∣ ((C (a i)*X+C (b i) : R[X])).coeff j := by
      by_cases hm : mark i
      · rcases j with _ | j
        · simpa [hm] using h i (Finset.mem_insert_self i S) hm
        · simp [hm]
      · simp [hm]
    have hc : ((insert i S).filter mark).card =
        (if mark i then 1 else 0)+(S.filter mark).card := by
      by_cases hm : mark i
      · have hn : i ∉ S.filter mark := fun he => hi (Finset.mem_filter.mp he).1
        simp [Finset.filter_insert, hm, hn, Nat.add_comm]
      · simp [Finset.filter_insert, hm]
    rw [Finset.prod_insert hi, hc]
    exact coeff_pow_lower_budget_mul q first small k

theorem integralNodal_dyadicCredit_dvd (T : Finset ℚ) (k : ℕ) :
    (2 : ℤ)^(dyadicCredit (dyadicDenCount T) (dyadicEvenCount T) k) ∣
      (integralRationalNodalHull T).coeff k := by
  have high := coeff_pow_sub_card_dvd_prod_linear (2 : ℤ) T
    (fun r => (r.den : ℤ)) (fun r => -r.num) denOdd
    (fun r _ hn => Int.natCast_dvd_natCast.mpr
      ((ZMod.natCast_eq_zero_iff r.den 2).mp (not_ne_iff.mp hn))) k
  have low := coeff_pow_lower_budget_prod_linear (2 : ℤ) T
    (fun r => (r.den : ℤ)) (fun r => -r.num) numEven
    (fun r _ hn => dvd_neg.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd r.num 2).mp hn)) k
  unfold dyadicCredit
  by_cases h : dyadicEvenCount T-k ≤ k-dyadicDenCount T
  · rw [max_eq_right h]
    exact high
  · rw [max_eq_left (le_of_not_ge h)]
    exact low

theorem integralNodal_map_two (T : Finset ℚ) :
    (integralRationalNodalHull T).map (Int.castRingHom (ZMod 2)) =
      (X : (ZMod 2)[X])^(dyadicEvenCount T) *
        (X+1)^(dyadicDenCount T-dyadicEvenCount T) := by
  have ev : (∏ r ∈ T, if numEven r then (X : (ZMod 2)[X]) else 1) =
      X^(dyadicEvenCount T) := by
    rw [Finset.prod_ite]
    simp [dyadicEvenCount]
  have od : (∏ r ∈ T, if denOdd r ∧ ¬numEven r then (X+1 : (ZMod 2)[X]) else 1) =
      (X+1)^(dyadicDenCount T-dyadicEvenCount T) := by
    rw [Finset.prod_ite]
    simp only [Finset.prod_const, one_pow, mul_one, dyadicOddNumeratorDenCount]
  rw [← ev, ← od, ← Finset.prod_mul_distrib]
  simp only [integralRationalNodalHull, Polynomial.map_prod, Polynomial.map_mul,
    Polynomial.map_add, Polynomial.map_X, Polynomial.map_C, Int.coe_castRingHom,
    Int.cast_natCast, Int.cast_neg]
  apply Finset.prod_congr rfl
  intro r _
  by_cases hd : denOdd r
  · have ds := (zmodTwo_choices (r.den : ZMod 2)).resolve_left hd
    by_cases hn : numEven r
    · simp [hd,hn,ds,numEven]
    · have ns := (zmodTwo_choices (r.num : ZMod 2)).resolve_left hn
      simp [hd,hn,ds,ns,zmodTwo_neg_one]
  · have ds := not_ne_iff.mp hd
    have hn : ¬ numEven r := fun h => hd (denOdd_of_numEven r h)
    have ns := (zmodTwo_choices (r.num : ZMod 2)).resolve_left hn
    simp [hd,ds,ns,zmodTwo_neg_one]

/-- Pure natural parity model of the binary reduction. -/
def dyadicParity (t u k : ℕ) : ℕ :=
  if u ≤ k then (Nat.fast_choose (t-u) (k-u)) % 2 else 0

theorem dyadicParity_lt_two (t u k : ℕ) : dyadicParity t u k < 2 := by
  unfold dyadicParity
  split
  · exact Nat.mod_lt _ (by decide)
  · decide

theorem integralNodal_coeff_two (T : Finset ℚ) (k : ℕ) :
    (((integralRationalNodalHull T).coeff k : ℤ) : ZMod 2) =
      (dyadicParity (dyadicDenCount T) (dyadicEvenCount T) k : ZMod 2) := by
  change (Int.castRingHom (ZMod 2)) ((integralRationalNodalHull T).coeff k) = _
  rw [← coeff_map, integralNodal_map_two, coeff_X_pow_mul']
  by_cases h : dyadicEvenCount T ≤ k
  · rw [if_pos h, dyadicParity, if_pos h, ZMod.natCast_mod, ← Nat.choose_eq_fast_choose]
    exact coeff_X_add_one_pow (ZMod 2) _ _
  · simp only [dyadicParity, if_neg h, Nat.cast_zero]

theorem rat_one_sub_den (r : ℚ) : (1-r).den = r.den := by
  apply Nat.dvd_antisymm
  · simpa using Rat.sub_den_dvd (1 : ℚ) r
  · simpa only [sub_sub_cancel, Rat.den_one, one_mul] using Rat.sub_den_dvd (1 : ℚ) (1-r)

theorem rat_one_sub_num (r : ℚ) : (1-r).num = (r.den : ℤ)-r.num := by
  apply Int.cast_injective (α := ℚ)
  calc
    _ = (((1-r).den : ℕ) : ℚ)*(1-r) := (Rat.den_mul_eq_num (1-r)).symm
    _ = (r.den : ℚ)-(r.num : ℚ) := by rw [rat_one_sub_den, mul_sub, mul_one, Rat.den_mul_eq_num]
    _ = _ := by simp

theorem denOdd_reflect_iff (r : ℚ) : denOdd (1-r) ↔ denOdd r := by
  change (((1-r).den : ℕ) : ZMod 2) ≠ 0 ↔ (r.den : ZMod 2) ≠ 0
  rw [rat_one_sub_den]

theorem numEven_reflect_iff (r : ℚ) : numEven (1-r) ↔ denOdd r ∧ ¬ numEven r := by
  change ((1-r).num : ZMod 2) = 0 ↔ _
  rw [rat_one_sub_num, Int.cast_sub, Int.cast_natCast, sub_eq_zero]
  by_cases hd : denOdd r
  · rw [(zmodTwo_choices (r.den : ZMod 2)).resolve_left hd]
    rcases zmodTwo_choices (r.num : ZMod 2) with hn | hn <;> simp [hd,numEven,hn]
  · have ds := not_ne_iff.mp hd
    have hn : ¬ numEven r := fun he => hd (denOdd_of_numEven r he)
    rw [ds,(zmodTwo_choices (r.num : ZMod 2)).resolve_left hn]
    simp [hd]

theorem dyadicCounts_reflect (T : Finset ℚ) :
    dyadicDenCount (T.image fun r => 1-r) = dyadicDenCount T ∧
    dyadicEvenCount (T.image fun r => 1-r) = dyadicDenCount T - dyadicEvenCount T := by
  have inj : Function.Injective (fun r : ℚ => 1-r) := by
    intro x y e
    simpa only [sub_sub_cancel] using congrArg (fun r : ℚ => 1-r) e
  constructor
  · unfold dyadicDenCount
    rw [Finset.filter_image, Finset.card_image_of_injective _ inj]
    apply congrArg Finset.card
    exact Finset.filter_congr fun r _ => denOdd_reflect_iff r
  · rw [← dyadicOddNumeratorDenCount T]
    unfold dyadicEvenCount
    rw [Finset.filter_image, Finset.card_image_of_injective _ inj]
    apply congrArg Finset.card
    exact Finset.filter_congr fun r _ => numEven_reflect_iff r

end RKResearch.Certified.DyadicFourShift
