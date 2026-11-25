module

public import RKCert.ReviewedNative.WeightXEightIrreducible
public import RKCert.ReviewedNative.NativeReciprocalResidueCut
public import Mathlib.FieldTheory.SplittingField.Construction

import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # The degree-eight polynomial's integral scaled reciprocal

If J is the previously derived Rodrigues polynomial, the integer
coefficients here are exactly T^8 J(9/T)/9. Its only residue certificate
is T^7(T+3) modulo 11. A single splitting field for the product supplies
both split polynomials, with no real-field or topology dependency.
-/
namespace RKCert.ReviewedNative.WeightXEight

open Polynomial RKResearch.Certified.Graded
open RKResearch.Certified.Graded.NativeReciprocal
noncomputable section

def reciprocalCoefficients (i : Fin 9) : ℤ :=
  if i.val=8 then 1 else coefficients ⟨8-i.val,by omega⟩ * 9^(7-i.val)

def integralReciprocal : ℤ[X] := ofFn 9 reciprocalCoefficients

private theorem recip_coeff (i : Fin 9) :
    integralReciprocal.coeff i.val=reciprocalCoefficients i :=
  ofFn_coeff_eq_val_of_lt _ i.isLt

private theorem recip_8 : integralReciprocal.coeff 8=1 := recip_coeff 8

private theorem recip_degree_le : integralReciprocal.natDegree≤8 :=
  Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) reciprocalCoefficients)

theorem integralReciprocal_monic : integralReciprocal.Monic :=
  monic_of_natDegree_le_of_coeff_eq_one 8 recip_degree_le recip_8

theorem integralReciprocal_mod11 :
    integralReciprocal.map (Int.castRingHom (ZMod 11)) =
      (X:(ZMod 11)[X])^7*(X+C 3) := by
  letI : Fact (Nat.Prime 11) := ⟨by decide⟩
  have base : (X:(ZMod 11)[X])^7*(X+C 3) = X^8+C 3*X^7 := by ring
  ext n
  by_cases hn : n<9
  · let i : Fin 9 := ⟨n,hn⟩
    change (integralReciprocal.map (Int.castRingHom (ZMod 11))).coeff i.val =
      ((X:(ZMod 11)[X])^7*(X+C 3)).coeff i.val
    have test (j : Fin 9) : (Int.castRingHom (ZMod 11)) (reciprocalCoefficients j) =
        (X^8 + C (3:ZMod 11)*X^7).coeff j.val := by
      fin_cases j <;> simp [reciprocalCoefficients,coefficients,coeff_C_mul,coeff_X_pow] <;> decide
    rw [coeff_map,recip_coeff,base]
    exact test i
  · have rhs : ((X:(ZMod 11)[X])^7*(X+C 3)).natDegree≤8 := by
      exact natDegree_mul_le.trans (by rw [natDegree_X_pow,natDegree_X_add_C])
    rw [coeff_map,coeff_eq_zero_of_natDegree_lt (recip_degree_le.trans_lt (by omega)),
      map_zero,coeff_eq_zero_of_natDegree_lt (rhs.trans_lt (by omega))]

private theorem base_coeff {E : Type*} [Field E] [CharZero E] (i : Fin 9) :
    (rationalPolynomial.map (algebraMap ℚ E)).coeff i.val =
      (24310:E)⁻¹*(coefficients i:E) := by
  rw [coeff_map,rationalPolynomial,coeff_C_mul,coeff_map,integral_coeff]
  change (algebraMap ℚ E) ((24310:ℚ)⁻¹*((coefficients i:ℤ):ℚ))=_
  simp

private theorem base_const {E : Type*} [Field E] [CharZero E] :
    (rationalPolynomial.map (algebraMap ℚ E)).coeff 0=(24310:E)⁻¹*9 := by
  simpa [coefficients] using base_coeff (E:=E) (0 : Fin 9)

theorem base_const_ne {E : Type*} [Field E] [CharZero E] :
    (rationalPolynomial.map (algebraMap ℚ E)).coeff 0≠0 := by
  rw [base_const]
  exact mul_ne_zero (inv_ne_zero (by norm_num)) (by norm_num)

theorem integralReciprocal_map {E : Type*} [Field E] [CharZero E] :
    integralReciprocal.map (algebraMap ℤ E) =
      scaledReciprocal (rationalPolynomial.map (algebraMap ℚ E)) 9 := by
  let H := rationalPolynomial.map (algebraMap ℚ E)
  have hn : H.coeff 0≠0 := base_const_ne
  have hd : H.natDegree=8 :=
    (natDegree_map_eq_of_injective (algebraMap ℚ E).injective _).trans rational_degree
  have sd : (scaledReciprocal H 9).natDegree=8 :=
    (scaledReciprocal_degree hn 9).trans hd
  ext n
  change (integralReciprocal.map (algebraMap ℤ E)).coeff n=(scaledReciprocal H 9).coeff n
  by_cases low : n≤8
  · by_cases high : n=8
    · subst n
      have top : (scaledReciprocal H 9).coeff 8=1 := by
        simpa only [sd] using (show (scaledReciprocal H 9).coeff (scaledReciprocal H 9).natDegree=1 by
          rw [coeff_natDegree, (scaledReciprocal_monic hn 9).leadingCoeff])
      rw [coeff_map,recip_8,map_one,top]
    · let i : Fin 9 := ⟨n,by omega⟩
      let j : Fin 9 := ⟨8-n,by omega⟩
      have paid : n≤H.natDegree := hd.symm ▸ low
      have ri : reciprocalCoefficients i = coefficients j*9^(7-n) := by
        simp only [reciprocalCoefficients,i,j,high,ite_false]
      have hj : H.coeff (8-n)=(24310:E)⁻¹*(coefficients j:E) := base_coeff j
      have hh : H.coeff 0=(24310:E)⁻¹*9 := base_const
      have b := recip_coeff i
      rw [coeff_map,b,ri,scaledReciprocal_coeff hn 9 paid,hd,hj,hh]
      change ((coefficients j*9^(7-n):ℤ):E)=_
      simp only [Int.cast_mul,Int.cast_pow,Int.cast_ofNat]
      rw [show 8-n=(7-n)+1 by omega,pow_succ]
      field_simp [show (9:E)≠0 by norm_num,show (24310:E)≠0 by norm_num] <;> ring
  · have lt := Nat.lt_of_not_ge low
    rw [coeff_map,coeff_eq_zero_of_natDegree_lt (recip_degree_le.trans_lt lt),
      map_zero,coeff_eq_zero_of_natDegree_lt (sd.le.trans_lt lt)]

def simultaneousPolynomial : ℚ[X] :=
  rationalPolynomial * integralReciprocal.map (algebraMap ℤ ℚ)

abbrev ResidueSplitField := simultaneousPolynomial.SplittingField

theorem residue_chosen_root :
    let E := ResidueSplitField
    let H := rationalPolynomial.map (algebraMap ℚ E)
    H.Splits ∧ ∃ v : E,H.IsRoot v ∧
      ∀ Q N : E[X], Q.natDegree=5 → Q*N=H → N.IsRoot v →
        (primitive (X*Q)).eval v≠0 := by
  let E := ResidueSplitField
  let H := rationalPolynomial.map (algebraMap ℚ E)
  let F := integralReciprocal.map (algebraMap ℤ E)
  have both : simultaneousPolynomial.map (algebraMap ℚ E)=H*F := by
    dsimp only [simultaneousPolynomial,H,F]
    rw [Polynomial.map_mul,map_map,←IsScalarTower.algebraMap_eq ℤ ℚ E]
  have simultaneous : (H*F).Splits :=
    both ▸ IsSplittingField.splits E simultaneousPolynomial
  have live : H*F≠0 := mul_ne_zero (rational_monic.map _).ne_zero
    (integralReciprocal_monic.map _).ne_zero
  have hs : H.Splits := simultaneous.of_dvd live ⟨F,rfl⟩
  have fs : F.Splits := simultaneous.of_dvd live ⟨H,mul_comm H F⟩
  exact ⟨hs,chosen_root_cut_of_integral_reciprocal H base_const_ne integralReciprocal
    integralReciprocal_monic integralReciprocal_map fs integralReciprocal_mod11⟩

end
end RKCert.ReviewedNative.WeightXEight
