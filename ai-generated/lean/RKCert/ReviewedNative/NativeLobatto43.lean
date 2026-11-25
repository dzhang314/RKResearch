module

public import RKCert.ReviewedNative.NativeModularRootLift

import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! # An exact small Lobatto pair certificate over characteristic zero

A cleared two-by-two minor replaces evaluation of the five-by-five
primitive determinant. It is tested at twenty ordered distinct simple
pairs modulo 43 and lifted at a single integral reduction place. -/

namespace RKResearch.Certified.Graded.NativeLobatto

open Polynomial NativeModularRootLift
open scoped BigOperators

variable {R S : Type*} [CommRing R] [CommRing S]

def lobattoValue (t : R) : R :=
  132*t^5 - 330*t^4 + 300*t^3 - 120*t^2 + 20*t - 1

def radauQuotient (t : R) : R :=
  1716*t^6 - 5544*t^5 + 6930*t^4 - 4200*t^3 + 1260*t^2 - 168*t + 7

def radauValue (t : R) : R := t * radauQuotient t

def cubicD (z : R) : R := (5*z-2)*(7*z-6)

def cubicN (z : R) : R := 100*z^4 - 460*z^3 + 819*z^2 - 672*z + 210

def pairNumerator (J : R → R) (t u : R) : R :=
  t^5 * (35*u^2 - 44*t*u + 12*t^2) * J u +
    u^3 * (100*u^4 - 460*t*u^3 + 819*t^2*u^2 - 672*t^3*u + 210*t^4) * J t

/-- Integer evaluation model for Y=132t, multiplying the degree-six
Radau quotient by 132^6. -/
def scaledRadau (x : R) : R :=
  1716*x^6 - 5544*132*x^5 + 6930*132^2*x^4 - 4200*132^3*x^3 +
    1260*132^4*x^2 - 168*132^5*x + 7*132^6

theorem map_pairNumerator_scaledRadau (f : R →+* S) (x y : R) :
    f (pairNumerator scaledRadau x y) = pairNumerator scaledRadau (f x) (f y) := by
  simp only [pairNumerator, scaledRadau, map_add, map_sub, map_mul, map_pow, map_ofNat]

private theorem scaledRadau_at (t : R) :
    scaledRadau (132*t) = (132:R)^6 * radauQuotient t := by
  unfold scaledRadau radauQuotient
  ring

private theorem pairNumerator_scaled (t u : R) :
    pairNumerator scaledRadau (132*t) (132*u) = (132:R)^13 * pairNumerator radauQuotient t u := by
  unfold pairNumerator
  rw [scaledRadau_at,scaledRadau_at]
  ring

def scaledCoefficients : Fin 6 → ℤ :=
  ![ -(132^4), 20*132^3, -(120*132^2), 300*132, -330, 1]

def scaledLobatto : ℤ[X] := ofFn 6 scaledCoefficients

private theorem scaled_coeff5 : scaledLobatto.coeff 5 = 1 := by
  rw [scaledLobatto, ofFn_coeff_eq_val_of_lt scaledCoefficients (by decide : 5 < 6)]
  decide

theorem scaledLobatto_monic : scaledLobatto.Monic :=
  monic_of_natDegree_le_of_coeff_eq_one 5
    (Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) scaledCoefficients)) scaled_coeff5

theorem scaledLobatto_degree : scaledLobatto.natDegree = 5 :=
  natDegree_eq_of_le_of_coeff_ne_zero
    (Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) scaledCoefficients))
    (by rw [scaled_coeff5]; decide)

private def scaledLobattoValue (x : R) : R :=
  x^5 - 330*x^4 + 300*132*x^3 - 120*132^2*x^2 + 20*132^3*x - 132^4

private theorem scaledLobatto_map_eval (f : ℤ →+* R) (x : R) :
    (scaledLobatto.map f).eval x = scaledLobattoValue x := by
  simp only [scaledLobatto, ofFn_eq_sum_monomial, Polynomial.map_sum,
    Polynomial.map_monomial, eval_finsetSum, eval_monomial, Fin.sum_univ_succ]
  simp [scaledCoefficients, scaledLobattoValue]
  <;> ring

private theorem scaledLobatto_at (t : R) :
    scaledLobattoValue (132*t) = (132:R)^4 * lobattoValue t := by
  unfold scaledLobattoValue lobattoValue
  ring

local instance : Fact (Nat.Prime 43) := ⟨by decide⟩
private abbrev z43 := Int.castRingHom (ZMod 43)

private def roots43 : Fin 5 → ZMod 43 := ![6,27,23,19,40]

private theorem roots43_injective : Function.Injective roots43 := by
  intro i j h
  revert h
  fin_cases i <;> fin_cases j <;> decide

private theorem roots43_root (i : Fin 5) :
    (scaledLobatto.map z43).IsRoot (roots43 i) := by
  change (scaledLobatto.map z43).eval (roots43 i)=0
  rw [scaledLobatto_map_eval]
  fin_cases i <;> decide

private theorem scaledLobatto_mod43 :
    scaledLobatto.map z43 = ∏ i : Fin 5, (X - C (roots43 i)) := by
  classical
  have pd : (∏ i : Fin 5, (X-C (roots43 i))).natDegree=5 := by
    rw [natDegree_prod_of_monic (Finset.univ : Finset (Fin 5))
      (fun i => (X : (ZMod 43)[X]) - C (roots43 i)) (fun i _ => monic_X_sub_C (roots43 i))]
    simp [natDegree_X_sub_C]
  have dv : (∏ i : Fin 5, (X-C (roots43 i))) ∣ scaledLobatto.map z43 := by
    apply Finset.prod_dvd_of_coprime
    · intro i _ j _ ne
      exact pairwise_coprime_X_sub_C roots43_injective ne
    · exact fun i _ => dvd_iff_isRoot.mpr (roots43_root i)
  apply eq_of_monic_of_dvd_of_natDegree_le
    (monic_prod_X_sub_C roots43 Finset.univ) (scaledLobatto_monic.map _) dv
  rw [scaledLobatto_monic.natDegree_map, scaledLobatto_degree, pd]

theorem scaledLobatto_mod43_separable : (scaledLobatto.map (Int.castRingHom (ZMod 43))).Separable := by
  rw [scaledLobatto_mod43]
  exact separable_prod (pairwise_coprime_X_sub_C roots43_injective)
    (fun _ => separable_X_sub_C)

/-- Closed checks of the twenty ordered residue pairs. The diagonal
cases in the finite enumeration are excluded, not tested for nonzero. -/
private theorem pair_nonzero43 (i j : Fin 5) :
    i ≠ j → pairNumerator scaledRadau (roots43 i) (roots43 j) ≠ 0 := by
  fin_cases i <;> fin_cases j <;> decide

private theorem residue_root_label {k : Type*} [Field k] [CharP k 43] {x : k}
    (root : (scaledLobatto.map (Int.castRingHom k)).IsRoot x) :
    ∃ i : Fin 5, x = ZMod.castHom (dvd_refl (43:ℕ)) k (roots43 i) := by
  classical
  let z := ZMod.castHom (dvd_refl (43:ℕ)) k
  have e : scaledLobatto.map (Int.castRingHom k) = (scaledLobatto.map z43).map z := by
    rw [Polynomial.map_map]
    exact congrArg (fun f : ℤ →+* k => scaledLobatto.map f) (RingHom.ext_int _ _)
  have h := root.eq_zero
  rw [e, scaledLobatto_mod43, Polynomial.map_prod, eval_prod] at h
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, eval_sub, eval_X, eval_C] at h
  obtain ⟨i, _, hr⟩ := Finset.prod_eq_zero_iff.mp h
  exact ⟨i, sub_eq_zero.mp hr⟩

private theorem pair_residue_ne_zero {k : Type*} [Field k] [CharP k 43] {x y : k}
    (hx : (scaledLobatto.map (Int.castRingHom k)).IsRoot x)
    (hy : (scaledLobatto.map (Int.castRingHom k)).IsRoot y) (ne : x≠y) :
    pairNumerator scaledRadau x y ≠ 0 := by
  obtain ⟨i, hi⟩ := residue_root_label hx
  obtain ⟨j, hj⟩ := residue_root_label hy
  let z := ZMod.castHom (dvd_refl (43:ℕ)) k
  have ij : i≠j := by
    intro e
    subst j
    exact ne (hi.trans hj.symm)
  rw [hi, hj, ← map_pairNumerator_scaledRadau z]
  intro bad
  exact pair_nonzero43 i j ij (z.injective (by simpa only [map_zero] using bad))

theorem pairNumerator_ne_zero_of_lobatto_roots {K : Type*} [Field K] [CharZero K]
    (t u : K) (ht : lobattoValue t = 0) (hu : lobattoValue u = 0) (different : t ≠ u) :
    pairNumerator radauQuotient t u ≠ 0 := by
  intro zero
  have hroot (x : K) (hx : lobattoValue x=0) :
      (scaledLobatto.map (algebraMap ℤ K)).IsRoot (132*x) := by
    change (scaledLobatto.map (algebraMap ℤ K)).eval (132*x)=0
    rw [scaledLobatto_map_eval,scaledLobatto_at,hx,mul_zero]
  have dist : (132:K)*t ≠ 132*u := fun e =>
    different (mul_left_cancel₀ (by norm_num : (132:K)≠0) e)
  refine with_distinct_monic_root_reduction 43 (by decide)
    scaledLobatto_monic scaledLobatto_mod43_separable (hroot t ht) (hroot u hu) dist ?_
  intro k _ _ q A B hA hB ha hb different'
  have neq := pair_residue_ne_zero ha hb different'
  let emb : integralClosure ℤ K →+* K := algebraMap (integralClosure ℤ K) K
  have inj : Function.Injective emb := fun _ _ h => Subtype.ext h
  have bad : pairNumerator scaledRadau A B = 0 := by
    apply inj
    rw [map_pairNumerator_scaledRadau, map_zero]
    change pairNumerator scaledRadau (A:K) (B:K)=0
    rw [hA,hB,pairNumerator_scaled,zero,mul_zero]
  apply neq
  rw [← map_pairNumerator_scaledRadau q,bad,map_zero]

theorem lobatto_root_ne_zero {K : Type*} [Field K] {t : K}
    (h : lobattoValue t = 0) : t ≠ 0 := by
  intro z
  rw [z] at h
  have hn : (-1:K) = 0 := by simpa [lobattoValue] using h
  exact one_ne_zero (neg_eq_zero.mp hn)

/-- Scalar form of the published five-row determinant, normalized by
the first nonzero knot. The equation keeps both high-mask leakage terms. -/
theorem normalized_cubic_minor_ne_zero {K : Type*} [Field K] [CharZero K]
    (t u : K) (ht : lobattoValue t = 0) (hu : lobattoValue u = 0) (different : t ≠ u) :
    cubicD (u/t) * radauValue u + (u/t)^4 * cubicN (u/t) * radauValue t ≠ 0 := by
  have t0 := lobatto_root_ne_zero ht
  have u0 := lobatto_root_ne_zero hu
  have h := pairNumerator_ne_zero_of_lobatto_roots t u ht hu different
  have factor : u * pairNumerator radauQuotient t u =
      t^7*(cubicD (u/t)*radauValue u+(u/t)^4*cubicN (u/t)*radauValue t) := by
    unfold pairNumerator cubicD cubicN radauValue
    field_simp [t0] <;> ring
  intro z
  rw [z,mul_zero] at factor
  exact mul_ne_zero u0 h factor

end RKResearch.Certified.Graded.NativeLobatto
