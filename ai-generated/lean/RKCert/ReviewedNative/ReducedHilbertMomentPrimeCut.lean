module

public import RKCert.ReviewedNative.FiniteCauchy
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Int.CharZero

import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Reduced Hilbert moments at a single exposed prime pole

Reduce only cleared integer identities. Above the finite reduction
degree, the primitive product's powers of the prime cancel the lone
paid denominator pole or make it vanish. No rational-to-residue ring
homomorphism is posited. -/

namespace RKResearch.Certified.RationalPrimeCut

open Polynomial
open scoped BigOperators Polynomial Classical

/-- A common denominator written as erased products, so no quotient
ring lift or integral division is needed for the regular terms. -/
private theorem sum_cast_eraseProd_eq_mul_sum_div {F ι : Type*} [Field F] [DecidableEq ι]
    (f : ℤ →+* F) (S : Finset ι) (a d : ι → ℤ)
    (hd : ∀ i ∈ S, f (d i) ≠ 0) :
    (∑ i ∈ S, f (a i * ∏ j ∈ S.erase i, d j)) =
      f (∏ i ∈ S, d i) * ∑ i ∈ S, f (a i) / f (d i) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  let E := ∏ j ∈ S.erase i, d j
  have hp : E * d i = ∏ j ∈ S, d j := Finset.prod_erase_mul S d hi
  rw [map_mul, ← hp, map_mul]
  calc
    f (a i) * f E = f E * f (a i) := mul_comm _ _
    _ = f E * ((f (a i) / f (d i)) * f (d i)) := by rw [div_mul_cancel₀ _ (hd i hi)]
    _ = _ := by ac_rfl

/-- A rational sum of integer ratios gives a literal integer relation. -/
theorem sum_int_eraseProd_zero_of_sum_rat_div_zero {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (a d : ι → ℤ) (hd : ∀ i ∈ S, d i ≠ 0)
    (hz : (∑ i ∈ S, (a i : ℚ) / (d i : ℚ)) = 0) :
    (∑ i ∈ S, a i * ∏ j ∈ S.erase i, d j) = 0 := by
  apply Int.cast_injective (α := ℚ)
  change Int.castRingHom ℚ _ = Int.castRingHom ℚ 0
  rw [map_sum, map_zero, sum_cast_eraseProd_eq_mul_sum_div (Int.castRingHom ℚ) S a d
    (fun i hi => Int.cast_ne_zero.mpr (hd i hi))]
  change ((∏ i ∈ S, d i : ℤ) : ℚ) * (∑ i ∈ S, (a i : ℚ) / (d i : ℚ)) = 0
  rw [hz, mul_zero]

/-- A rational zero-sum of integer ratios survives any field image
in which each actual denominator remains nonzero. -/
theorem sum_div_int_reduces_zero {F ι : Type*} [Field F] [DecidableEq ι]
    (f : ℤ →+* F) (S : Finset ι) (a d : ι → ℤ)
    (hd : ∀ i ∈ S, f (d i) ≠ 0)
    (hz : (∑ i ∈ S, (a i : ℚ) / (d i : ℚ)) = 0) :
    (∑ i ∈ S, f (a i) / f (d i)) = 0 := by
  have hi := sum_int_eraseProd_zero_of_sum_rat_div_zero S a d
    (fun i hi e => hd i hi (by rw [e, map_zero])) hz
  have hm := congrArg f hi
  rw [map_sum, map_zero, sum_cast_eraseProd_eq_mul_sum_div f S a d hd] at hm
  have hp : f (∏ i ∈ S, d i) ≠ 0 := by
    rw [map_prod]
    exact Finset.prod_ne_zero_iff.mpr hd
  exact (mul_eq_zero.mp hm).resolve_left hp

/-- The paid uniform row for integer polynomial coefficients before reduction. -/
def UniformIntRowZero (a : ℕ → ℤ) (n k : ℕ) : Prop :=
  (∑ j ∈ Finset.range (n+1), (a j : ℚ) / ((j+k+1 : ℕ) : ℚ)) = 0

/-- The corresponding residue-field row in its ordinary coefficient chart. -/
def UniformZModRowZero (q : ℕ) [Fact q.Prime] (a : ℕ → ZMod q) (n k : ℕ) : Prop :=
  (∑ j ∈ Finset.range (n+1), a j / ((j+k+1 : ℕ) : ZMod q)) = 0

private theorem zmod_natCast_ne_of_lt_two_mul {q d : ℕ}
    (hpos : 0 < d) (hlt : d < 2*q) (hne : d ≠ q) : (d : ZMod q) ≠ 0 := by
  intro hz
  obtain ⟨w, hw⟩ := (ZMod.natCast_eq_zero_iff d q).mp hz
  have hmul : q*w < q*2 := by rwa [← hw, Nat.mul_comm q 2]
  have hwlt := Nat.lt_of_mul_lt_mul_left hmul
  have hwne : w ≠ 0 := fun e => (Nat.ne_of_gt hpos) (by simp [hw, e])
  exact hne (by rw [hw, show w = 1 by omega, mul_one])

private theorem zmod_natCast_ne_of_pos_lt {q d : ℕ} (hp : 0 < d) (hlt : d < q) :
    (d : ZMod q) ≠ 0 := by
  intro h
  have he := congrArg ZMod.val h
  rw [ZMod.val_natCast_of_lt hlt, ZMod.val_zero] at he
  exact (Nat.ne_of_gt hp) he

/-- At the only possible denominator pole, the reduced numerator must
vanish. The product with that one denominator erased is a residue unit. -/
theorem coeff_mod_zero_of_uniform_single_pole {q n k j : ℕ} [Fact q.Prime]
    (a : ℕ → ℤ) (hbound : n+k+1 < 2*q) (hj : j ≤ n) (hjp : j+k+1 = q)
    (hz : UniformIntRowZero a n k) : (a j : ZMod q) = 0 := by
  let S := Finset.range (n+1)
  let d (i : ℕ) : ℤ := (i+k+1 : ℕ)
  have hd (i : ℕ) (_ : i ∈ S) : d i ≠ 0 :=
    Int.natCast_ne_zero.mpr (by omega)
  have hInt := sum_int_eraseProd_zero_of_sum_rat_div_zero S a d hd
    (by simpa only [S, d, UniformIntRowZero, Int.cast_natCast] using hz)
  have hRed := congrArg (Int.castRingHom (ZMod q)) hInt
  simp only [map_sum, map_mul, map_prod, map_zero, d, Int.coe_castRingHom,
    Int.cast_natCast] at hRed
  have hjS : j ∈ S := Finset.mem_range.mpr (by omega)
  rw [Finset.sum_eq_single_of_mem j hjS] at hRed
  · refine (mul_eq_zero.mp hRed).resolve_right (Finset.prod_ne_zero_iff.mpr ?_)
    intro i hi
    have hb := Finset.mem_range.mp (Finset.mem_erase.mp hi).2
    have hn := (Finset.mem_erase.mp hi).1
    apply zmod_natCast_ne_of_lt_two_mul
    · omega
    · omega
    · omega
  · intro i _ hij
    have hmem : j ∈ S.erase i := Finset.mem_erase.mpr ⟨hij.symm, hjS⟩
    have hzprod : (∏ l ∈ S.erase i, ((l+k+1 : ℕ) : ZMod q)) = 0 :=
      Finset.prod_eq_zero hmem (by rw [hjp, ZMod.natCast_self])
    rw [hzprod, mul_zero]

/-- If the only pole sits at least two coefficients above the retained
degree, division by the pole still leaves a zero residue. -/
theorem reduce_uniform_row_of_square_tail {q n r k : ℕ} [Fact q.Prime]
    (a : ℕ → ℤ) (hr : r ≤ n) (hbound : n+k+1 < 2*q) (hsafe : r+k+2 < q)
    (hmod : ∀ j : ℕ, r < j → (a j : ZMod q) = 0)
    (hpow : ∀ j : ℕ, r+1 < j → (q : ℤ)^2 ∣ a j)
    (hz : UniformIntRowZero a n k) :
    UniformZModRowZero q (fun j => (a j : ZMod q)) r k := by
  let S := Finset.range (n+1)
  let num (i : ℕ) : ℤ := if i+k+1=q then a i/(q : ℤ) else a i
  let den (i : ℕ) : ℤ := if i+k+1=q then 1 else (i+k+1 : ℕ)
  have hprime : q.Prime := Fact.out
  have hqZ : (q : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hprime.ne_zero
  have regular (i : ℕ) (hi : i ∈ S) : (den i : ZMod q) ≠ 0 := by
    by_cases e : i+k+1=q
    · simp [den, e]
    · have hlt := Finset.mem_range.mp hi
      simp only [den, ite_eq_right e, Int.cast_natCast]
      exact zmod_natCast_ne_of_lt_two_mul (by omega) (by omega) e
  have patched : (∑ i ∈ S, (num i : ℚ) / (den i : ℚ)) = 0 := by
    unfold UniformIntRowZero at hz
    rw [← hz]
    apply Finset.sum_congr rfl
    intro i _
    by_cases e : i+k+1=q
    · have hsq := hpow i (by omega)
      have hd : (q : ℤ) ∣ a i := (dvd_pow_self (q : ℤ) (by decide : (2 : ℕ) ≠ 0)).trans hsq
      simp only [num, den, ite_eq_left e, Int.cast_one, div_one, Int.cast_div_charZero hd,
        Int.cast_natCast, e]
    · simp only [num, den, ite_eq_right e, Int.cast_natCast]
  have he : (∑ j ∈ S, (num j : ZMod q) / (den j : ZMod q)) = 0 := by
    simpa only [Int.coe_castRingHom] using
      sum_div_int_reduces_zero (Int.castRingHom (ZMod q)) S num den
        (fun i hi => by simpa only [Int.coe_castRingHom] using regular i hi) patched
  change (∑ j ∈ Finset.range (r+1), (a j : ZMod q) / ((j+k+1 : ℕ) : ZMod q)) = 0
  calc
    _ = ∑ j ∈ Finset.range (r+1), (num j : ZMod q) / (den j : ZMod q) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hlt := Finset.mem_range.mp hj
      have no : j+k+1 ≠ q := by omega
      simp only [num, den, ite_eq_right no, Int.cast_natCast]
    _ = ∑ j ∈ S, (num j : ZMod q) / (den j : ZMod q) := by
      apply Finset.sum_subset (Finset.range_subset_range.mpr (by omega))
      intro j _ hnone
      have hle : r+1 ≤ j := by simpa only [Finset.mem_range, not_lt] using hnone
      have hlt : r < j := by omega
      by_cases e : j+k+1=q
      · obtain ⟨v, hv⟩ := hpow j (by omega)
        have hquo : a j/(q : ℤ) = (q : ℤ)*v := by
          rw [hv, pow_two, mul_assoc, Int.mul_ediv_cancel_left _ hqZ]
        simp only [num, ite_eq_left e, hquo, Int.cast_mul, Int.cast_natCast,
          ZMod.natCast_self, zero_mul, zero_div]
      · simp only [num, ite_eq_right e, hmod j hlt, zero_div]
    _ = 0 := he

/-- Prime projection of an integral nodal coefficient list with the
coefficient tail budget. The last row can fail only at `r+t+1=q`. -/
theorem reduced_Hilbert_projection {q n t : ℕ} [Fact q.Prime]
    (P : ℤ[X]) (hnq : n < q) (hpaid : n+t < 2*q) (hdeg : P.natDegree ≤ n)
    (hR : P.map (Int.castRingHom (ZMod q)) ≠ 0)
    (hpow : ∀ j : ℕ, (q : ℤ)^(j-(P.map (Int.castRingHom (ZMod q))).natDegree) ∣ P.coeff j)
    (law : ∀ k : ℕ, k < t → UniformIntRowZero P.coeff n k) :
    let r := (P.map (Int.castRingHom (ZMod q))).natDegree
    r+t < q ∧
      ∀ k : ℕ, k < t → r+k+2 < q →
        UniformZModRowZero q (fun j => (P.coeff j : ZMod q)) r k := by
  dsimp only
  let R := P.map (Int.castRingHom (ZMod q))
  let r := R.natDegree
  have hr : r ≤ n := (show R.natDegree ≤ P.natDegree from natDegree_map_le).trans hdeg
  have hlead : (P.coeff r : ZMod q) ≠ 0 := by
    change Int.castRingHom (ZMod q) (P.coeff r) ≠ 0
    rw [← coeff_map, coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hR
  have hcut : r+t < q := by
    by_contra h
    let k := q-1-r
    have hk : k < t := by dsimp only [k]; omega
    have hPole : r+k+1 = q := by dsimp only [k]; omega
    exact hlead (coeff_mod_zero_of_uniform_single_pole P.coeff (by omega) hr hPole (law k hk))
  refine ⟨hcut, ?_⟩
  intro k hk hsafe
  apply reduce_uniform_row_of_square_tail P.coeff hr (by omega) hsafe _ _ (law k hk)
  · intro j hj
    change Int.castRingHom (ZMod q) (P.coeff j) = 0
    rw [← coeff_map]
    exact coeff_eq_zero_of_natDegree_lt hj
  · intro j hj
    exact (pow_dvd_pow (q : ℤ) (show 2 ≤ j-r by omega)).trans (hpow j)

/-- The ordinary finite Hilbert block detects every coefficient as soon
as its full denominator range is strictly below the prime. -/
theorem reduced_Hilbert_detect {q r : ℕ} [Fact q.Prime] (hpay : 2*r+1 < q)
    (a : ℕ → ZMod q) (h : ∀ k : ℕ, k ≤ r → UniformZModRowZero q a r k) :
    ∀ j : ℕ, j ≤ r → a j = 0 := by
  let x (i : Fin (r+1)) : ZMod q := (i.val : ZMod q)
  let y (j : Fin (r+1)) : ZMod q := (j.val : ZMod q)+1
  have xinj : Function.Injective x := by
    intro i j hij
    have hi : i.val < q := by have := i.isLt; omega
    have hj : j.val < q := by have := j.isLt; omega
    have he := congrArg ZMod.val hij
    change (((i.val : ℕ) : ZMod q)).val = (((j.val : ℕ) : ZMod q)).val at he
    rw [ZMod.val_natCast_of_lt hi, ZMod.val_natCast_of_lt hj] at he
    exact Fin.ext he
  have yinj : Function.Injective y := by
    intro i j hij
    apply xinj
    exact add_right_cancel hij
  have hn (i j : Fin (r+1)) : x i+y j ≠ 0 := by
    have hh : (((i.val+j.val+1 : ℕ) : ZMod q)) ≠ 0 :=
      zmod_natCast_ne_of_pos_lt (by omega) (by have := i.isLt; have := j.isLt; omega)
    simpa only [x, y, Nat.cast_add, Nat.cast_one, add_assoc] using hh
  have ht (i : Fin (r+1)) : (∑ j : Fin (r+1), a j.val/(x i+y j)) = 0 := by
    have he := h i.val (by have := i.isLt; omega)
    unfold UniformZModRowZero at he
    rw [← Fin.sum_univ_eq_sum_range
      (fun j => a j/((j+i.val+1 : ℕ) : ZMod q)) (r+1)] at he
    simpa only [x, y, Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using he
  intro j hj
  exact RKResearch.Certified.Graded.cauchy_kernel x y (fun i => a i.val)
    xinj yinj hn ht ⟨j, Nat.lt_succ_of_le hj⟩

/-- The strict classification of a projected nonzero polynomial's
row prefix is independent of how the projection was obtained. -/
theorem strict_prime_Hilbert_of_projection {q t : ℕ} [Fact q.Prime]
    (R : (ZMod q)[X]) (hne : R ≠ 0) (hcut : R.natDegree+t < q) (hgap : q < 2*t)
    (law : ∀ k : ℕ, k < t → R.natDegree+k+2 < q → UniformZModRowZero q R.coeff R.natDegree k) :
    False := by
  have htop := reduced_Hilbert_detect (by omega : 2*R.natDegree+1 < q) R.coeff
    (fun k hk => law k (by omega) (by omega)) R.natDegree le_rfl
  rw [coeff_natDegree] at htop
  exact (leadingCoeff_ne_zero.mpr hne) htop

/-- The strict prime gap for any integral coefficient list with the
nodal coefficient power budget. -/
theorem strict_prime_Hilbert_obstruction {q n t : ℕ} [Fact q.Prime]
    (P : ℤ[X]) (hnq : n < q) (hpaid : n+t < 2*q) (hgap : q < 2*t)
    (hdeg : P.natDegree ≤ n) (hR : P.map (Int.castRingHom (ZMod q)) ≠ 0)
    (hpow : ∀ j : ℕ, (q : ℤ)^(j-(P.map (Int.castRingHom (ZMod q))).natDegree) ∣ P.coeff j)
    (law : ∀ k : ℕ, k < t → UniformIntRowZero P.coeff n k) : False := by
  let R := P.map (Int.castRingHom (ZMod q))
  obtain ⟨hcut, rows⟩ := reduced_Hilbert_projection P hnq hpaid hdeg hR hpow law
  apply strict_prime_Hilbert_of_projection R hR hcut hgap
  intro k hk hsafe
  simpa only [UniformZModRowZero, R, coeff_map, Int.coe_castRingHom] using rows k hk hsafe

end RKResearch.Certified.RationalPrimeCut
