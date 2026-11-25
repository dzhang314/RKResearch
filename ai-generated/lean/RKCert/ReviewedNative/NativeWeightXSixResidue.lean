module

public import RKCert.ReviewedNative.GradedPrimitives

import RKCert.ReviewedNative.NativePrimitiveMoments
import RKCert.ReviewedNative.NativePrimitiveRootTransport
import RKCert.ReviewedNative.NativeReciprocalCoefficientCut
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GroupWithZero.Associated
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # A standalone six-moment first-primitive cut over characteristic zero

The six literal native weight-X moments recognize the monic sextic.
Eisenstein at 7 and a single nonleading coefficient modulo 5 give
the selected-root cuts for factor degrees three and four.
No tableau geometry or scalar replay is imported. -/

namespace RKResearch.Certified.Graded.NativeWeightXSix

open Polynomial RKResearch.Certified.Graded.NativeMoments
open RKResearch.Certified.Graded.NativeReciprocal RKResearch.Certified.Graded.NativeRootTransport
open scoped BigOperators Classical

noncomputable section

private def coefficients : Fin 7 → ℤ :=
  ![7,-168,1260,-4200,6930,-5544,1716]

private def J : ℤ[X] := ofFn 7 coefficients

private theorem jCoeff (i : Fin 7) : J.coeff i.val = coefficients i :=
  ofFn_coeff_eq_val_of_lt _ i.isLt

private theorem j0 : J.coeff 0 = 7 := jCoeff 0
private theorem j6 : J.coeff 6 = 1716 := jCoeff 6

private theorem jDegree : J.natDegree = 6 :=
  natDegree_eq_of_le_of_coeff_ne_zero
    (Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) coefficients))
    (by rw [j6]; decide)

private theorem jLead : J.leadingCoeff = 1716 := by
  rw [← coeff_natDegree, jDegree, j6]

private theorem jPrimitive : J.IsPrimitive := by
  apply isPrimitive_iff_isUnit_of_C_dvd.mpr
  intro a ha
  have h0 := (C_dvd_iff_dvd_coeff _ _).mp ha 0
  have h6 := (C_dvd_iff_dvd_coeff _ _).mp ha 6
  rw [j0] at h0
  rw [j6] at h6
  have h := dvd_sub h6 (dvd_mul_of_dvd_right h0 245)
  apply isUnit_iff_dvd_one.mpr
  convert h using 1 <;> norm_num

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private abbrev z7 := Int.castRingHom (ZMod 7)
private abbrev z5 := Int.castRingHom (ZMod 5)

private theorem jMod7 : J.map z7 = (X : (ZMod 7)[X])^6 := by
  ext n
  by_cases low : n < 7
  · let i : Fin 7 := ⟨n,low⟩
    change (J.map z7).coeff i.val = ((X : (ZMod 7)[X])^6).coeff i.val
    have atIndex (j : Fin 7) :
        z7 (coefficients j) = ((X : (ZMod 7)[X])^6).coeff j.val := by
      fin_cases j <;> simp [z7, coefficients, coeff_X_pow] <;> decide
    rw [coeff_map, jCoeff]
    exact atIndex i
  · rw [coeff_map, show J.coeff n = 0 from ofFn_coeff_eq_zero_of_ge _ (by omega),
      map_zero, coeff_eq_zero_of_natDegree_lt (by rw [natDegree_X_pow]; omega)]

private theorem unit_of_constant_factor {U V : ℤ[X]} (fac : J = U * V)
    (d : U.natDegree = 0) : IsUnit U := by
  have e := eq_C_of_natDegree_eq_zero d
  have dv : C (U.coeff 0) ∣ J :=
    ⟨V, fac.trans (congrArg (fun P : ℤ[X] => P * V) e)⟩
  exact e.symm ▸ isUnit_C.mpr (isPrimitive_iff_isUnit_of_C_dvd.mp jPrimitive _ dv)

private theorem mod7_constant_of_positive_factor {P : (ZMod 7)[X]}
    (pd : 0 < P.natDegree) (dvd : P ∣ (X : (ZMod 7)[X])^6) :
    P.coeff 0 = 0 := by
  obtain ⟨i,_,assoc⟩ := (dvd_prime_pow (prime_X : Prime (X : (ZMod 7)[X])) 6).mp dvd
  have e : P.natDegree = i := by
    rw [natDegree_eq_of_degree_eq (degree_eq_degree_of_associated assoc), natDegree_X_pow]
  have ip : 0 < i := by rwa [← e]
  exact X_dvd_iff.mp ((dvd_pow_self _ (Nat.ne_of_gt ip)).trans assoc.symm.dvd)

-- The ordinary Eisenstein argument on this sextic, using cached polynomial
-- APIs rather than importing an additional Eisenstein dependency.
private theorem jIrreducible : Irreducible J := by
  refine ⟨?_,?_⟩
  · intro u
    have d := natDegree_eq_zero_of_isUnit u
    rw [jDegree] at d
    omega
  · intro U V fac
    by_cases u0 : U.natDegree = 0
    · exact Or.inl (unit_of_constant_factor fac u0)
    by_cases v0 : V.natDegree = 0
    · exact Or.inr (unit_of_constant_factor (fac.trans (mul_comm U V)) v0)
    have maps : U.map z7 * V.map z7 = (X : (ZMod 7)[X])^6 := by
      rw [← Polynomial.map_mul, ← fac, jMod7]
    have lc : z7 U.leadingCoeff * z7 V.leadingCoeff ≠ 0 := by
      rw [← map_mul, ← leadingCoeff_mul, ← fac, jLead]
      decide
    have ud := natDegree_map_of_leadingCoeff_ne_zero z7 (mul_ne_zero_iff.mp lc).1
    have vd := natDegree_map_of_leadingCoeff_ne_zero z7 (mul_ne_zero_iff.mp lc).2
    have zu : (U.map z7).coeff 0 = 0 :=
      mod7_constant_of_positive_factor (by rw [ud]; omega) ⟨V.map z7,maps.symm⟩
    have zv : (V.map z7).coeff 0 = 0 :=
      mod7_constant_of_positive_factor (by rw [vd]; omega)
        ⟨U.map z7,maps.symm.trans (mul_comm _ _)⟩
    have du : (7 : ℤ) ∣ U.coeff 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (U.coeff 0) 7).mp (by rw [coeff_map] at zu; exact zu)
    have dv : (7 : ℤ) ∣ V.coeff 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (V.coeff 0) 7).mp (by rw [coeff_map] at zv; exact zv)
    have ce : (U * V).coeff 0 = U.coeff 0 * V.coeff 0 := by
      simp only [coeff_zero_eq_eval_zero, eval_mul]
    have bad : (49 : ℤ) ∣ U.coeff 0 * V.coeff 0 := mul_dvd_mul du dv
    rw [← ce, ← fac, j0] at bad
    exact False.elim ((by decide : ¬ (49 : ℤ) ∣ 7) bad)

private def H : ℚ[X] := C ((1716 : ℚ)⁻¹) * J.map (Int.castRingHom ℚ)

private theorem hMonic : H.Monic := by
  change H.leadingCoeff = 1
  rw [H, leadingCoeff_mul, leadingCoeff_C,
    leadingCoeff_map_of_injective (show Function.Injective (Int.castRingHom ℚ) from Int.cast_injective),
    jLead]
  norm_num

private theorem hDegree : H.natDegree = 6 := by
  rw [H, natDegree_C_mul (by norm_num),
    natDegree_map_eq_of_injective (show Function.Injective (Int.castRingHom ℚ) from Int.cast_injective),
    jDegree]

private theorem hIrreducible : Irreducible H := by
  unfold H
  apply (irreducible_isUnit_mul (isUnit_C.mpr
    (isUnit_iff_ne_zero.mpr (by norm_num : (1716 : ℚ)⁻¹ ≠ 0)))).mpr
  exact (IsPrimitive.Int.irreducible_iff_irreducible_map_cast jPrimitive).mp jIrreducible

private theorem hDegreeMap {K : Type*} [Field K] [CharZero K] :
    (H.map (algebraMap ℚ K)).natDegree = 6 :=
  (natDegree_map_eq_of_injective (algebraMap ℚ K).injective H).trans hDegree

private theorem jMoment (i : Fin 6) :
    (primitive ((X : ℚ[X])^i.val * (X * J.map (Int.castRingHom ℚ)))).eval 1 = 0 := by
  let a : Fin 7 → ℚ := fun j => (coefficients j : ℚ)
  have rep : J.map (Int.castRingHom ℚ) = ofFn 7 a := by
    simp only [J, ofFn_eq_sum_monomial, Polynomial.map_sum, Polynomial.map_monomial, a] <;> rfl
  rw [rep, show (X : ℚ[X]) * ofFn 7 a = X^1 * ofFn 7 a by rw [pow_one]]
  have expansion (i : Fin 6) :
      (primitive ((X : ℚ[X])^i.val * (X^1 * ofFn 7 a))).eval 1 =
        ∑ j : Fin 7, a j / ((i.val + j.val + 2 : ℕ) : ℚ) := by
    rw [← mul_assoc, ← pow_add, ofFn_eq_sum_monomial,
      Finset.mul_sum, map_sum, eval_finsetSum]
    apply Finset.sum_congr rfl
    intro j _
    rw [X_pow_mul_monomial, primitive_monomial, eval_monomial, one_pow, mul_one]
    congr 2
    omega
  rw [expansion]
  fin_cases i <;> norm_num [a, coefficients, Fin.sum_univ_succ]

private theorem hMoment (i : Fin 6) :
    (primitive ((X : ℚ[X])^i.val * (X * H))).eval 1 = 0 := by
  have eq : (X : ℚ[X])^i.val * (X * H) =
      (1716 : ℚ)⁻¹ • ((X : ℚ[X])^i.val * (X * J.map (Int.castRingHom ℚ))) := by
    rw [H, smul_eq_C_mul]
    ring
  change (Polynomial.leval (1 : ℚ)) (primitive ((X : ℚ[X])^i.val * (X * H))) = 0
  rw [eq, map_smul, map_smul,
    show (Polynomial.leval (1 : ℚ)) (primitive ((X : ℚ[X])^i.val *
      (X * J.map (Int.castRingHom ℚ)))) = 0 from jMoment i,
    smul_zero]

private theorem hMomentMap {K : Type*} [Field K] [CharZero K] (i : Fin 6) :
    (primitive ((X : K[X])^i.val * (X * H.map (algebraMap ℚ K)))).eval 1 = 0 := by
  let f := algebraMap ℚ K
  have z : ((primitive ((X : ℚ[X])^i.val * (X * H))).map f).eval (f 1) = 0 := by
    rw [eval_map_apply, hMoment, map_zero]
  simpa only [f, primitive_map, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, map_one]
    using z

private def reciprocalCoeffs : Fin 7 → ℤ :=
  ![1716*7^5,-5544*7^4,6930*7^3,-4200*7^2,1260*7,-168,1]

private def F : ℤ[X] := ofFn 7 reciprocalCoeffs

private theorem fCoeff (i : Fin 7) : F.coeff i.val = reciprocalCoeffs i :=
  ofFn_coeff_eq_val_of_lt _ i.isLt

private theorem fDegreeLe : F.natDegree ≤ 6 :=
  Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) reciprocalCoeffs)

private theorem fMonic : F.Monic :=
  monic_of_natDegree_le_of_coeff_eq_one 6 fDegreeLe (fCoeff 6)

private theorem fMod5 : F.map z5 = ((X : (ZMod 5)[X]) + C 1)^5 * (X + C 2) := by
  have frob : ((X : (ZMod 5)[X]) + C 1)^5 = X^5 + C 1 := by
    rw [add_pow_char _ _ 5, ← C_pow, one_pow]
  have shape : ((X : (ZMod 5)[X]) + C 1)^5 * (X + C 2) =
      X^6 + C 2 * X^5 + X + C 2 := by
    rw [frob]
    simp only [map_one]
    ring
  have deg : (((X : (ZMod 5)[X]) + C 1)^5 * (X + C 2)).natDegree = 6 := by
    rw [natDegree_mul ((monic_X_add_C (1 : ZMod 5)).pow 5).ne_zero
      (monic_X_add_C (2 : ZMod 5)).ne_zero, natDegree_pow_X_add_C, natDegree_X_add_C]
  ext n
  by_cases low : n < 7
  · let i : Fin 7 := ⟨n,low⟩
    change (F.map z5).coeff i.val = (((X : (ZMod 5)[X]) + C 1)^5 * (X + C 2)).coeff i.val
    have atIndex (j : Fin 7) : z5 (reciprocalCoeffs j) =
        (X^6 + C (2 : ZMod 5) * X^5 + X + C 2).coeff j.val := by
      fin_cases j <;> simp [z5, reciprocalCoeffs, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C] <;> decide
    rw [coeff_map, fCoeff, shape]
    exact atIndex i
  · rw [coeff_map, show F.coeff n = 0 from ofFn_coeff_eq_zero_of_ge _ (by omega),
      map_zero, coeff_eq_zero_of_natDegree_lt (by rw [deg]; omega)]

private theorem hCoeffMap {E : Type*} [Field E] [CharZero E] (i : Fin 7) :
    (H.map (algebraMap ℚ E)).coeff i.val = (1716 : E)⁻¹ * (coefficients i : E) := by
  rw [coeff_map, H, coeff_C_mul, coeff_map, jCoeff]
  change (algebraMap ℚ E) ((1716 : ℚ)⁻¹ * ((coefficients i : ℤ) : ℚ)) = _
  simp

private theorem hConst {E : Type*} [Field E] [CharZero E] :
    (H.map (algebraMap ℚ E)).coeff 0 = (1716 : E)⁻¹ * 7 := by
  simpa [coefficients] using hCoeffMap (E := E) (0 : Fin 7)

private theorem hConstNe {E : Type*} [Field E] [CharZero E] :
    (H.map (algebraMap ℚ E)).coeff 0 ≠ 0 := by
  rw [hConst]
  exact mul_ne_zero (inv_ne_zero (by norm_num)) (by norm_num)

private theorem fMap {E : Type*} [Field E] [CharZero E] :
    F.map (algebraMap ℤ E) = scaledReciprocal (H.map (algebraMap ℚ E)) 7 := by
  let HK := H.map (algebraMap ℚ E)
  have hd : HK.natDegree = 6 := hDegreeMap
  have hn : HK.coeff 0 ≠ 0 := hConstNe
  have sd : (scaledReciprocal HK 7).natDegree = 6 := (scaledReciprocal_degree hn 7).trans hd
  ext n
  change (F.map (algebraMap ℤ E)).coeff n = (scaledReciprocal HK 7).coeff n
  by_cases low : n < 7
  · suffices h : ∀ i : Fin 7,
        (F.map (algebraMap ℤ E)).coeff i.val = (scaledReciprocal HK 7).coeff i.val from h ⟨n, low⟩
    intro i
    have le : i.val ≤ HK.natDegree := by rw [hd]; exact Nat.le_of_lt_succ i.isLt
    let j : Fin 7 := ⟨6-i.val,by omega⟩
    have cj : HK.coeff (6-i.val) = (1716 : E)⁻¹ * (coefficients j : E) := hCoeffMap j
    have c0 : HK.coeff 0 = (1716 : E)⁻¹ * 7 := hConst
    rw [coeff_map, fCoeff, scaledReciprocal_coeff hn 7 le, hd, cj, c0]
    fin_cases i <;> simp [reciprocalCoeffs, coefficients, j] <;> norm_num <;>
      field_simp <;> ring
  · have high : 6 < n := by omega
    rw [coeff_map, coeff_eq_zero_of_natDegree_lt (fDegreeLe.trans_lt high), map_zero,
      coeff_eq_zero_of_natDegree_lt (sd.le.trans_lt high)]

private def rates : Fin 5 → ℤ := ![30,20,15,12,10]

private theorem rates_clear (i : Fin 5) :
    rates i * ((i.val + 1 + 1 : ℕ) : ℤ) = 60 := by
  fin_cases i <;> decide

private theorem residue_value :
    (∑ i : Fin 5, (rates i : ZMod 5) *
      ((4 : ℕ).choose (4-i.val) : ZMod 5) * (-2 : ZMod 5)^(4-i.val)) = 4 := by
  norm_num [rates, Fin.sum_univ_succ] <;> decide

private theorem residue_test {k : Type*} [Field k] [CharP k 5]
    (z : ZMod 5 →+* k) (S : k[X]) (sm : S.Monic) (sd : S.natDegree = 4)
    (dv : S ∣ ((X : k[X]) + C 1)^5) :
    (∑ i : Fin 5, (rates i : k) * S.coeff (4-i.val) * (-2 : k)^(4-i.val)) ≠ 0 := by
  have prime : Prime ((X : k[X]) + C 1) := by
    simpa only [map_neg, sub_neg_eq_add] using (prime_X_sub_C (-1 : k))
  obtain ⟨i,_,assoc⟩ := (dvd_prime_pow prime 5).mp dv
  have shape := eq_of_monic_of_associated sm ((monic_X_add_C (1 : k)).pow i) assoc
  have id : i = 4 := by rw [← sd, shape, natDegree_pow_X_add_C]
  rw [id] at shape
  rw [shape]
  simp only [coeff_X_add_C_pow, one_pow, one_mul]
  have eq : (∑ j : Fin 5, (rates j : k) *
      ((4 : ℕ).choose (4-j.val) : k) * (-2 : k)^(4-j.val)) = 4 := by
    simpa only [map_sum, map_mul, map_pow, map_intCast, map_natCast, map_neg, map_ofNat] using
      congrArg z residue_value
  rw [eq]
  exact fun h => (by decide : ¬(5 : ℕ) ∣ 4) ((CharP.cast_eq_zero_iff k 5 4).mp h)

private def rates3 : Fin 4 → ℤ := ![30,20,15,12]

private theorem rates3_clear (i : Fin 4) :
    rates3 i * ((i.val + 1 + 1 : ℕ) : ℤ) = 60 := by
  fin_cases i <;> decide

private theorem residue3_value :
    (∑ i : Fin 4, (rates3 i : ZMod 5) *
      ((3 : ℕ).choose (3-i.val) : ZMod 5) * (-2 : ZMod 5)^(3-i.val)) = 2 := by
  norm_num [rates3, Fin.sum_univ_succ] <;> decide

private theorem residue3_test {k : Type*} [Field k] [CharP k 5]
    (z : ZMod 5 →+* k) (S : k[X]) (sm : S.Monic) (sd : S.natDegree = 3)
    (dv : S ∣ ((X : k[X]) + C 1)^5) :
    (∑ i : Fin 4, (rates3 i : k) * S.coeff (3-i.val) * (-2 : k)^(3-i.val)) ≠ 0 := by
  have prime : Prime ((X : k[X]) + C 1) := by
    simpa only [map_neg, sub_neg_eq_add] using (prime_X_sub_C (-1 : k))
  obtain ⟨i,_,assoc⟩ := (dvd_prime_pow prime 5).mp dv
  have shape := eq_of_monic_of_associated sm ((monic_X_add_C (1 : k)).pow i) assoc
  have id : i = 3 := by rw [← sd, shape, natDegree_pow_X_add_C]
  rw [id] at shape
  rw [shape]
  simp only [coeff_X_add_C_pow, one_pow, one_mul]
  have eq : (∑ j : Fin 4, (rates3 j : k) *
      ((3 : ℕ).choose (3-j.val) : k) * (-2 : k)^(3-j.val)) = 2 := by
    simpa only [map_sum, map_mul, map_pow, map_intCast, map_natCast, map_neg, map_ofNat] using
      congrArg z residue3_value
  rw [eq]
  exact fun h => (by decide : ¬(5 : ℕ) ∣ 2) ((CharP.cast_eq_zero_iff k 5 2).mp h)

private theorem five_not_unit (E : Type*) [Field E] [CharZero E] :
    ¬IsUnit (5 : integralClosure ℤ E) := by
  intro h
  let B := integralClosure ℤ E
  obtain ⟨z,hz⟩ := isUnit_iff_exists_inv.mp h
  have ez : (5 : E)*(z : E) = 1 := by
    have e := congrArg (algebraMap B E) hz
    simpa only [map_mul, map_ofNat, map_one, Subalgebra.algebraMap_apply] using e
  have zn : (5 : E) ≠ 0 := by norm_num
  have asRat : (z : E)∈Set.range (Rat.cast : ℚ → E) := by
    refine ⟨(5 : ℚ)⁻¹,?_⟩
    have e : (((5 : ℚ)⁻¹ : ℚ) : E) = (5 : E)⁻¹ := by
      rw [Rat.cast_inv, Rat.cast_ofNat]
    rw [e]
    apply mul_left_cancel₀ zn
    rw [mul_inv_cancel₀ zn, ez]
  have iz : IsIntegral ℤ (z : E) := z.2
  obtain ⟨n,hn⟩ := iz.mem_range_ratCast_iff.mp asRat
  have int : (5 : ℤ)*n = 1 := by
    apply (Int.cast_injective : Function.Injective (fun i : ℤ => (i : E)))
    simp only [Int.cast_mul, Int.cast_ofNat, Int.cast_one]
    rw [hn]
    exact ez
  exact (by decide : ¬(5 : ℤ) ∣ 1) ⟨n,int.symm⟩

private def joint : ℚ[X] := H * F.map (algebraMap ℤ ℚ)
private abbrev E₆ := joint.SplittingField

private theorem chosen_cut_of_residue (d : ℕ) (rate : Fin (d+1) → ℤ)
    (paid : ∀ i : Fin (d+1), rate i * ((i.val + 1 + 1 : ℕ) : ℤ) = 60)
    (check : ∀ {k : Type} [Field k] [CharP k 5],
      (ZMod 5 →+* k) → ∀ S : k[X], S.Monic → S.natDegree = d →
      S ∣ ((X : k[X]) + C 1)^5 →
      (∑ i : Fin (d+1), (rate i : k) * S.coeff (d-i.val) * (-2 : k)^(d-i.val)) ≠ 0) :
    let HK := H.map (algebraMap ℚ E₆)
    HK.Splits ∧ ∃ v : E₆, HK.IsRoot v ∧
      ∀ P N : E₆[X], P.natDegree = d → P * N = HK → N.IsRoot v →
        (primitive (X * P)).eval v ≠ 0 := by
  let HK := H.map (algebraMap ℚ E₆)
  let FE := F.map (algebraMap ℤ E₆)
  have both : joint.map (algebraMap ℚ E₆) = HK*FE := by
    dsimp only [joint, HK, FE]
    rw [Polynomial.map_mul, map_map, ← IsScalarTower.algebraMap_eq ℤ ℚ E₆]
  have split : (HK*FE).Splits := both ▸ IsSplittingField.splits E₆ joint
  have live : HK*FE ≠ 0 := mul_ne_zero (hMonic.map _).ne_zero (fMonic.map _).ne_zero
  have hs : HK.Splits := split.of_dvd live ⟨FE,rfl⟩
  have fs : FE.Splits := split.of_dvd live ⟨HK,mul_comm HK FE⟩
  let B := integralClosure ℤ E₆
  let I : Ideal B := Ideal.span {(5 : B)}
  have proper : I ≠ ⊤ := fun top => five_not_unit E₆ (Ideal.span_singleton_eq_top.mp top)
  obtain ⟨m,maximal,inc⟩ := Ideal.exists_le_maximal I proper
  letI : m.IsMaximal := maximal
  let k := B ⧸ m
  letI : Field k := Ideal.Quotient.field m
  let q : B →+* k := Ideal.Quotient.mk m
  have eq5 : (5 : k) = 0 := by
    have mem : (5 : B)∈m := inc (Ideal.subset_span (by simp [I]))
    have eq : q (5 : B) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr mem
    simpa only [map_ofNat] using eq
  letI : CharP k 5 := (CharP.charP_iff_prime_eq_zero (by decide : Nat.Prime 5)).mpr eq5
  let z := ZMod.castHom (dvd_refl (5 : ℕ)) k
  have red : (F.map (algebraMap ℤ B)).map q =
      ((X : k[X]) + C 1)^5 * (X - C (-2)) := by
    have eq : q.comp (algebraMap ℤ B) = z.comp z5 := RingHom.ext_int _ _
    rw [map_map, eq, ← map_map, fMod5]
    have ztwo : z (2 : ZMod 5) = (2 : k) := map_ofNat z 2
    simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_add, Polynomial.map_C, Polynomial.map_one, map_one, ztwo, map_neg, sub_neg_eq_add]
  have two : (2 : k) ≠ 0 := fun h =>
    (by decide : ¬(5 : ℕ) ∣ 2) ((CharP.cast_eq_zero_iff k 5 2).mp h)
  obtain ⟨v,hv,test⟩ := chosen_root_cut_of_reduced_coefficients HK hConstNe F fMonic
    (by norm_num : (7 : E₆) ≠ 0) fMap fs q (neg_ne_zero.mpr two)
    (((X : k[X]) + C 1)^5) red d 1 60 rate paid (check z)
  refine ⟨hs,v,hv,?_⟩
  intro P N pd pn nr
  simpa only [pow_one] using test P N pd pn nr

private theorem chosen_cut (d : ℕ) (supported : d = 3 ∨ d = 4) :
    let HK := H.map (algebraMap ℚ E₆)
    HK.Splits ∧ ∃ v : E₆, HK.IsRoot v ∧
      ∀ P N : E₆[X], P.natDegree = d → P * N = HK → N.IsRoot v →
        (primitive (X * P)).eval v ≠ 0 := by
  rcases supported with rfl | rfl
  · exact chosen_cut_of_residue 3 rates3 rates3_clear residue3_test
  · exact chosen_cut_of_residue 4 rates rates_clear residue_test

private def weightMoment {K : Type*} [Field K] (i : ℕ) : K[X] →ₗ[K] K :=
  (Polynomial.leval (1 : K)).comp (primitive.comp
    ((LinearMap.mulLeft K ((X : K[X])^i)).comp (LinearMap.mulLeft K X)))

private theorem first_primitive_nonzero_of_six_moments_aux
    {K : Type*} [Field K] [CharZero K] (P N : K[X]) (u : K)
    (d : ℕ) (supported : d = 3 ∨ d = 4)
    (pd : P.natDegree = d) (nd : N.natDegree = 6-d) (root : N.IsRoot u)
    (test : ∀ i : Fin 6, (primitive (X^i.val * (X * (P * N)))).eval 1 = 0) :
    (primitive (X * P)).eval u ≠ 0 := by
  intro zero
  have pn : P ≠ 0 := by intro e; rw [e,natDegree_zero] at pd; omega
  have nn : N ≠ 0 := by intro e; rw [e,natDegree_zero] at nd; omega
  have pl := leadingCoeff_ne_zero.mpr pn
  have nl := leadingCoeff_ne_zero.mpr nn
  let P' := C (P.leadingCoeff⁻¹) * P
  let N' := C (N.leadingCoeff⁻¹) * N
  have pM : P'.Monic := by
    change (C (P.leadingCoeff⁻¹) * P).leadingCoeff = 1
    rw [leadingCoeff_mul, leadingCoeff_C, inv_mul_cancel₀ pl]
  have nM : N'.Monic := by
    change (C (N.leadingCoeff⁻¹) * N).leadingCoeff = 1
    rw [leadingCoeff_mul, leadingCoeff_C, inv_mul_cancel₀ nl]
  have pd' : P'.natDegree = d := by
    dsimp only [P']; rw [natDegree_C_mul (inv_ne_zero pl), pd]
  have nd' : N'.natDegree = 6-d := by
    dsimp only [N']; rw [natDegree_C_mul (inv_ne_zero nl), nd]
  have dProd : (P' * N').natDegree = 6 := by
    rw [natDegree_mul pM.ne_zero nM.ne_zero, pd', nd']
    omega
  have mProd : (P' * N').Monic := pM.mul nM
  have scale : P' * N' = (P.leadingCoeff⁻¹ * N.leadingCoeff⁻¹) • (P * N) := by
    dsimp only [P', N']
    rw [smul_eq_C_mul, C_mul]
    ring
  have normalized (i : Fin 6) : weightMoment i.val (P' * N') = 0 := by
    rw [scale, map_smul, show weightMoment i.val (P * N) = 0 from test i, smul_zero]
  let HK := H.map (algebraMap ℚ K)
  have hkM : HK.Monic := hMonic.map _
  have hkD : HK.natDegree = 6 := hDegreeMap
  have tD : (P' * N' - HK).natDegree ≤ 5 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    rw [coeff_sub]
    by_cases eq : i = 6
    · subst i
      have top : (P' * N').coeff 6 = 1 := by rw [← dProd, coeff_natDegree, mProd]
      have htop : HK.coeff 6 = 1 := by rw [← hkD, coeff_natDegree, hkM]
      rw [top, htop, sub_self]
    · rw [coeff_eq_zero_of_natDegree_lt (show (P' * N').natDegree < i by omega),
        coeff_eq_zero_of_natDegree_lt (show HK.natDegree < i by omega), sub_zero]
  have product : P' * N' = HK := by
    apply sub_eq_zero.mp
    apply x_moments_detect (n := 5) tD
    intro i
    change weightMoment i.val (P' * N' - HK) = 0
    rw [map_sub, normalized i, show weightMoment i.val HK = 0 from hMomentMap i, sub_zero]
  have nroot : N'.IsRoot u := by
    change (C (N.leadingCoeff⁻¹) * N).eval u = 0
    rw [eval_mul, root.eq_zero, mul_zero]
  have pzero : (primitive (X * P')).eval u = 0 := by
    have eq : X * P' = (P.leadingCoeff⁻¹) • (X * P) := by
      dsimp only [P']; rw [smul_eq_C_mul]; ring
    change (Polynomial.leval u) (primitive (X * P')) = 0
    rw [eq, map_smul, map_smul, show (Polynomial.leval u) (primitive (X * P)) = 0 from zero, smul_zero]
  obtain ⟨hs,v,hv,cut⟩ := chosen_cut d supported
  obtain ⟨P₁,N₁,_,_,dp,_,pr,nr,zr⟩ :=
    transport_first_primitive_zero H hMonic hIrreducible pM nM product nroot pzero hs hv
  exact cut P₁ N₁ (dp.trans pd') pr nr zr

/-- Six native weight-X moments exclude a first primitive zero for the
quartic profile at a root of its quadratic complement. -/
theorem first_primitive_nonzero_of_six_moments
    {K : Type*} [Field K] [CharZero K] (P N : K[X]) (u : K)
    (pd : P.natDegree = 4) (nd : N.natDegree = 2) (root : N.IsRoot u)
    (test : ∀ i : Fin 6, (primitive (X^i.val * (X * (P * N)))).eval 1 = 0) :
    (primitive (X * P)).eval u ≠ 0 :=
  first_primitive_nonzero_of_six_moments_aux P N u 4 (Or.inr rfl) pd nd root test

/-- The same six native moments exclude the cubic/cubic first port.
At the selected residue root, the term with denominator five is now
the constant coefficient of the cubic reciprocal factor. -/
theorem first_cubic_primitive_nonzero_of_six_moments
    {K : Type*} [Field K] [CharZero K] (P N : K[X]) (u : K)
    (pd : P.natDegree = 3) (nd : N.natDegree = 3) (root : N.IsRoot u)
    (test : ∀ i : Fin 6, (primitive (X^i.val * (X * (P * N)))).eval 1 = 0) :
    (primitive (X * P)).eval u ≠ 0 :=
  first_primitive_nonzero_of_six_moments_aux P N u 3 (Or.inl rfl) pd nd root test

end
end RKResearch.Certified.Graded.NativeWeightXSix
