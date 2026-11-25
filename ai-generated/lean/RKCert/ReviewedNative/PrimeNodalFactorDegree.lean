module

public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Algebra.Polynomial.Degree.SmallDegree
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Rat.Cast.CharZero

import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Elementary degree and coefficient divisibility of reduced nodal products

The coefficient budgets add under convolution. For factors whose slopes
vanish modulo a prime, this proves the exact power-divisibility bound
without a valuation type or a choice of lifts of residue-field roots. -/

namespace RKResearch.Certified.RationalPrimeCut

open Polynomial
open scoped Polynomial BigOperators Classical

/-- Coefficient divisibility budgets add under polynomial multiplication. -/
theorem coeff_pow_sub_dvd_mul {R : Type*} [CommSemiring R]
    (q : R) {P Q : R[X]} {r s : ℕ}
    (hP : ∀ j : ℕ, q^(j-r) ∣ P.coeff j) (hQ : ∀ j : ℕ, q^(j-s) ∣ Q.coeff j)
    (k : ℕ) : q^(k-(r+s)) ∣ (P*Q).coeff k := by
  rw [coeff_mul]
  apply Finset.dvd_sum
  intro ij hij
  have hsum := Finset.mem_antidiagonal.mp hij
  refine (pow_dvd_pow q (show k-(r+s) ≤ (ij.1-r)+(ij.2-s) by omega)).trans ?_
  rw [pow_add]
  exact mul_dvd_mul (hP ij.1) (hQ ij.2)

private theorem linear_coeff_pow_sub_dvd {R : Type*} [CommSemiring R]
    (q a b : R) (good : Prop) [Decidable good] (hbad : ¬good → q ∣ a)
    (j : ℕ) : q^(j-(if good then 1 else 0)) ∣ ((C a)*X+C b : R[X]).coeff j := by
  rcases j with _ | j
  · simp
  rcases j with _ | j
  · by_cases h : good
    · simp [h]
    · simpa [h, coeff_add, coeff_C_mul_X, coeff_C_succ] using hbad h
  · have hd : ((C a)*X+C b : R[X]).natDegree ≤ 1 := natDegree_linear_le
    rw [coeff_eq_zero_of_natDegree_lt (hd.trans_lt (by omega))]
    exact dvd_zero _

/-- Only the factors with good slopes contribute a free coefficient
degree; all other factors buy a power of `q` for each degree used. -/
theorem coeff_pow_sub_card_dvd_prod_linear {R ι : Type*} [CommSemiring R]
    (q : R) (S : Finset ι) (a b : ι → R) (good : ι → Prop) [DecidablePred good]
    (hbad : ∀ i ∈ S, ¬good i → q ∣ a i) :
    ∀ j : ℕ, q^(j-(S.filter good).card) ∣
      (∏ i ∈ S, (C (a i) * X + C (b i) : R[X])).coeff j := by
  revert hbad
  induction S using Finset.induction_on with
  | empty =>
    intro _ j
    simp only [Finset.filter_empty, Finset.card_empty, Nat.sub_zero, Finset.prod_empty, coeff_one]
    cases j <;> simp
  | @insert i S hi ih =>
    intro h j
    have small := ih (fun l hl => h l (Finset.mem_insert_of_mem hl))
    have first := linear_coeff_pow_sub_dvd q (a i) (b i) (good i)
      (h i (Finset.mem_insert_self i S))
    have hc : ((insert i S).filter good).card = (if good i then 1 else 0)+(S.filter good).card := by
      by_cases hg : good i
      · have off : i ∉ S.filter good := fun hh => hi (Finset.mem_filter.mp hh).1
        simp [Finset.filter_insert, hg, off, Nat.add_comm]
      · simp [Finset.filter_insert, hg]
    rw [Finset.prod_insert hi, hc]
    exact coeff_pow_sub_dvd_mul q first small j

/-- Reduction sends each primitive linear factor to a nonzero
constant or a genuinely linear polynomial. Collisions of finite
roots do not change the degree or the splitting assertion. -/
theorem map_prod_linear_profile {R F ι : Type*} [CommSemiring R] [Field F]
    (f : R →+* F) (S : Finset ι) (a b : ι → R)
    (primitive : ∀ i ∈ S, f (a i) ≠ 0 ∨ f (b i) ≠ 0) :
    let Q := (∏ i ∈ S, (C (a i) * X + C (b i) : R[X])).map f
    Q ≠ 0 ∧ Q.Splits ∧ Q.natDegree = (S.filter (fun i => f (a i) ≠ 0)).card := by
  dsimp only
  simp only [Polynomial.map_prod, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_X]
  let L (i : ι) : F[X] := C (f (a i)) * X + C (f (b i))
  change (∏ i ∈ S, L i) ≠ 0 ∧ (∏ i ∈ S, L i).Splits ∧
    (∏ i ∈ S, L i).natDegree = (S.filter (fun i => f (a i) ≠ 0)).card
  have nd (i : ι) : (L i).natDegree = if f (a i) ≠ 0 then 1 else 0 := by
    by_cases h : f (a i) = 0
    · simp [L, h]
    · simpa only [ite_eq_left h] using
        (natDegree_linear (b := f (b i)) h : (L i).natDegree = 1)
  have nz (i : ι) (hi : i ∈ S) : L i ≠ 0 := by
    by_cases h : f (a i) = 0
    · simpa [L, h, C_ne_zero] using (primitive i hi).resolve_left (not_ne_iff.mpr h)
    · intro hz
      have hh := nd i
      rw [hz, natDegree_zero, ite_eq_left h] at hh
      exact Nat.zero_ne_one hh
  refine ⟨Finset.prod_ne_zero_iff.mpr nz, Splits.prod (fun i _ => ?_), ?_⟩
  · exact Splits.of_natDegree_le_one (natDegree_linear_le (a := f (a i)) (b := f (b i)))
  · rw [Polynomial.natDegree_prod S L nz]
    simp only [nd]
    rw [← Finset.sum_filter]
    simp

/-- Clear denominators one rational root at a time, so each factor
is primitive at every prime, not merely primitive after a global choice. -/
noncomputable def integralRationalNodalHull (T : Finset ℚ) : ℤ[X] :=
  ∏ x ∈ T, (C (x.den : ℤ) * X + C (-x.num))

theorem integralRationalNodalHull_natDegree (T : Finset ℚ) :
    (integralRationalNodalHull T).natDegree = T.card := by
  let L (x : ℚ) : ℤ[X] := C (x.den : ℤ) * X + C (-x.num)
  have nd (x : ℚ) : (L x).natDegree = 1 :=
    natDegree_linear (Int.natCast_ne_zero.mpr x.den_ne_zero)
  have nz (x : ℚ) (_ : x ∈ T) : L x ≠ 0 := by
    intro hh
    have he := nd x
    rw [hh, natDegree_zero] at he
    exact Nat.zero_ne_one he
  change (∏ x ∈ T, L x).natDegree = T.card
  rw [Polynomial.natDegree_prod T L nz]
  simp [nd]

theorem integralRationalNodalHull_eval₂_zero {K : Type*} [Field K] [CharZero K]
    {T : Finset ℚ} {x : ℚ} (hx : x ∈ T) :
    (integralRationalNodalHull T).eval₂ (Int.castRingHom K) (x : K) = 0 := by
  unfold integralRationalNodalHull
  rw [eval₂_finsetProd]
  apply Finset.prod_eq_zero hx
  have e := congrArg (Rat.castHom K) (Rat.den_mul_eq_num x)
  simp only [map_mul, map_natCast, map_intCast] at e
  simp only [Rat.coe_castHom] at e
  change ((C (x.den : ℤ) * X + C (-x.num) : ℤ[X]).eval₂ (Int.castRingHom K) (x : K)) = 0
  simp only [eval₂_add, eval₂_mul, eval₂_X, eval₂_C, Int.coe_castRingHom, Int.cast_natCast,
    Int.cast_neg, e, add_neg_cancel]

/-- Denominator-unit count, exact reduction degree, and the coefficient
power bound for the actual primitive nodal product. -/
theorem integralRationalNodalHull_mod_profile (q : ℕ) [Fact q.Prime] (T : Finset ℚ) :
    let P := integralRationalNodalHull T
    let Q := P.map (Int.castRingHom (ZMod q))
    Q ≠ 0 ∧ Q.Splits ∧
      Q.natDegree = (T.filter (fun x => (x.den : ZMod q) ≠ 0)).card ∧
      ∀ j : ℕ, (q : ℤ)^(j-Q.natDegree) ∣ P.coeff j := by
  dsimp only
  let f := Int.castRingHom (ZMod q)
  have primitive (x : ℚ) (_ : x ∈ T) :
      f (x.den : ℤ) ≠ 0 ∨ f (-x.num) ≠ 0 := by
    by_cases h : f (x.den : ℤ) = 0
    · right
      intro hneg
      have hd : q ∣ x.den := (ZMod.natCast_eq_zero_iff x.den q).mp
        (by simpa only [f, Int.coe_castRingHom, Int.cast_natCast] using h)
      have hn' : (x.num : ZMod q) = 0 :=
        neg_eq_zero.mp (by simpa only [f, Int.coe_castRingHom, Int.cast_neg] using hneg)
      have hn : q ∣ x.num.natAbs :=
        Int.ofNat_dvd_left.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd x.num q).mp hn')
      exact (Fact.out : q.Prime).ne_one ((Nat.gcd_eq_one_iff.mp x.reduced) q hn hd)
    · exact Or.inl h
  have hp := map_prod_linear_profile f T (fun x => (x.den : ℤ)) (fun x => -x.num) primitive
  change ((integralRationalNodalHull T).map f) ≠ 0 ∧
    ((integralRationalNodalHull T).map f).Splits ∧
    ((integralRationalNodalHull T).map f).natDegree =
      (T.filter (fun x => (x.den : ZMod q) ≠ 0)).card ∧ _
  dsimp only at hp
  have hd : ((integralRationalNodalHull T).map f).natDegree =
      (T.filter (fun x => (x.den : ZMod q) ≠ 0)).card := by
    simpa only [f, Int.coe_castRingHom, Int.cast_natCast, integralRationalNodalHull] using hp.2.2
  refine ⟨hp.1, hp.2.1, hd, ?_⟩
  rw [hd]
  exact coeff_pow_sub_card_dvd_prod_linear (q : ℤ) T (fun x => (x.den : ℤ))
    (fun x => -x.num) (fun x => (x.den : ZMod q) ≠ 0) (fun x _ h =>
      Int.natCast_dvd_natCast.mpr
        ((ZMod.natCast_eq_zero_iff x.den q).mp (not_ne_iff.mp h)))

end RKResearch.Certified.RationalPrimeCut
