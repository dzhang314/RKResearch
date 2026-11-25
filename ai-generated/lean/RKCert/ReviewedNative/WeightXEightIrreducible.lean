module

public import Mathlib.Algebra.Polynomial.OfFn
public import Mathlib.RingTheory.Polynomial.GaussLemma

import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Data.Fin.VecNotation
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # The single degree-eight weight-X polynomial is irreducible

The coefficients are the independent Rodrigues expansion
`(-1)^(8-k) * choose 8 k * choose (9+k) 8`. Modulo 11 a surviving
leading coefficient restricts any factor to degree at most one. Modulo
3, the bottom three integral coefficients exclude the linear factor.
There is no factor, norm, endpoint-test, or determinant table.
-/
namespace RKCert.ReviewedNative.WeightXEight

open Polynomial
noncomputable section

def coefficients : Fin 9 → ℤ :=
  ![9,-360,4620,-27720,90090,-168168,180180,-102960,24310]

def integralPolynomial : ℤ[X] := ofFn 9 coefficients

theorem integral_coeff (i : Fin 9) :
    integralPolynomial.coeff i.val=coefficients i :=
  ofFn_coeff_eq_val_of_lt _ i.isLt

private theorem j0 : integralPolynomial.coeff 0=9 := integral_coeff 0
private theorem j1 : integralPolynomial.coeff 1= -360 := integral_coeff 1
private theorem j2 : integralPolynomial.coeff 2=4620 := integral_coeff 2
private theorem j8 : integralPolynomial.coeff 8=24310 := integral_coeff 8

theorem integral_degree : integralPolynomial.natDegree=8 :=
  natDegree_eq_of_le_of_coeff_ne_zero
    (Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) coefficients))
    (by rw [j8]; decide)

theorem integral_lead : integralPolynomial.leadingCoeff=24310 := by
  rw [← coeff_natDegree,integral_degree,j8]

private theorem integral_primitive : integralPolynomial.IsPrimitive := by
  apply isPrimitive_iff_isUnit_of_C_dvd.mpr
  intro a ha
  have h0 := (C_dvd_iff_dvd_coeff _ _).mp ha 0
  have h8 := (C_dvd_iff_dvd_coeff _ _).mp ha 8
  rw [j0] at h0
  rw [j8] at h8
  have h := dvd_sub h8 (dvd_mul_of_dvd_right h0 2701)
  apply isUnit_iff_dvd_one.mpr
  convert h using 1 <;> norm_num

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : Fact (Nat.Prime 11) := ⟨by decide⟩

private abbrev z3 := Int.castRingHom (ZMod 3)
private abbrev z11 := Int.castRingHom (ZMod 11)

private theorem mod3_shape : integralPolynomial.map z3 = (X : (ZMod 3)[X])^8 := by
  ext n
  by_cases b : n<9
  · let i : Fin 9 := ⟨n,b⟩
    change (integralPolynomial.map z3).coeff i.val=((X:(ZMod 3)[X])^8).coeff i.val
    have test (j : Fin 9) : z3 (coefficients j) = ((X : (ZMod 3)[X])^8).coeff j.val := by
      fin_cases j <;> simp [z3,coefficients,coeff_X_pow] <;> decide
    rw [coeff_map,integral_coeff]
    exact test i
  · have high : 8<n := by omega
    rw [coeff_map,show integralPolynomial.coeff n=0 from
      ofFn_coeff_eq_zero_of_ge _ (by omega),map_zero,
      coeff_eq_zero_of_natDegree_lt (by rwa [natDegree_X_pow])]

private theorem mod11_shape : integralPolynomial.map z11 =
    (C (9 : ZMod 11)+C (3 : ZMod 11)*X) := by
  ext n
  by_cases b : n<9
  · let i : Fin 9 := ⟨n,b⟩
    change (integralPolynomial.map z11).coeff i.val=(C (9 : ZMod 11)+C 3*X).coeff i.val
    have test (j : Fin 9) : z11 (coefficients j) = (C (9 : ZMod 11)+C 3*X).coeff j.val := by
      fin_cases j <;> simp [z11,coefficients,coeff_C_mul,coeff_X] <;> decide
    rw [coeff_map,integral_coeff]
    exact test i
  · have hG : (C (9:ZMod 11)+C 3*X).natDegree≤1 :=
      natDegree_add_le_of_le (p:=C (9 : ZMod 11)) (q:=C (3 : ZMod 11)*X)
        (by rw [natDegree_C]) ((natDegree_C_mul_le (3 : ZMod 11) X).trans natDegree_X.le)
    rw [coeff_map,show integralPolynomial.coeff n=0 from
      ofFn_coeff_eq_zero_of_ge _ (by omega),map_zero,
      coeff_eq_zero_of_natDegree_lt (hG.trans_lt (by omega))]

private theorem cancel_three_squared {a f : ℤ} (an : ¬(3:ℤ)∣a)
    (h : (9:ℤ)∣a*f) : (9:ℤ)∣f := by
  have h3 : (3:ℤ)∣a*f := dvd_trans (by decide : (3:ℤ)∣9) h
  obtain ⟨x,hx⟩ := (Int.Prime.dvd_mul' (p:=3) (by decide) h3).resolve_left an
  obtain ⟨y,hy⟩ := h
  have equation : (3:ℤ)*(a*x)=3*(3*y) := by
    calc
      _=a*f := by rw [hx]; ring
      _=9*y := hy
      _=_ := by ring
  have eq := mul_left_cancel₀ (show (3:ℤ)≠0 by decide) equation
  obtain ⟨u,hu⟩ := (Int.Prime.dvd_mul' (p:=3) (by decide) ⟨y,eq⟩).resolve_left an
  exact ⟨u,by rw [hx,hu]; ring⟩

private theorem no_linear_factor {F G : ℤ[X]} (fac : integralPolynomial=F*G)
    (gD : G.natDegree=1) : False := by
  let a := G.coeff 1
  let b := G.coeff 0
  have shape : G=C a*X+C b :=
    eq_X_add_C_of_degree_le_one (G.degree_le_natDegree.trans (by simp [gD]))
  have lead : G.leadingCoeff=a := by rw [← coeff_natDegree,gD]
  have eqLead : F.leadingCoeff*a=24310 := by
    rw [← lead,← leadingCoeff_mul,← fac,integral_lead]
  have aNot : ¬(3:ℤ)∣a := by
    intro ha
    have z := dvd_mul_of_dvd_right ha F.leadingCoeff
    rw [eqLead] at z
    exact (by decide : ¬(3:ℤ)∣24310) z
  let a3 : ZMod 3 := a
  let b3 : ZMod 3 := b
  have an : a3≠0 := fun az => aNot ((ZMod.intCast_zmod_eq_zero_iff_dvd a 3).mp az)
  let r := -b3/a3
  have gRoot : (G.map z3).eval r=0 := by
    rw [shape,Polynomial.map_add,Polynomial.map_mul,Polynomial.map_X,
      Polynomial.map_C,Polynomial.map_C,eval_add,eval_mul,eval_C,eval_X,eval_C]
    change a3*(-b3/a3)+b3=0
    field_simp [an] <;> ring
  have rp : r^8=0 := by
    have h := congrArg (fun P : (ZMod 3)[X] => P.eval r) (congrArg (Polynomial.map z3) fac)
    simpa only [mod3_shape,Polynomial.map_mul,eval_mul,gRoot,mul_zero,eval_pow,eval_X] using h
  have rz : r=0 := eq_zero_of_pow_eq_zero rp
  have bb : b3=0 := by
    rw [rz,shape,Polynomial.map_add,Polynomial.map_mul,Polynomial.map_X,
      Polynomial.map_C,Polynomial.map_C,eval_add,eval_mul,eval_C,eval_X,
      mul_zero,zero_add,eval_C] at gRoot
    exact gRoot
  have bd : (3:ℤ)∣b := (ZMod.intCast_zmod_eq_zero_iff_dvd b 3).mp bb
  have at0 : b*F.coeff 0=9 := by
    rw [←j0,fac,mul_comm F G,shape,add_mul,mul_assoc]
    simp only [coeff_add,coeff_C_mul,coeff_X_mul_zero,mul_zero,zero_add]
  have at1 : a*F.coeff 0+b*F.coeff 1= -360 := by
    rw [←j1,fac,mul_comm F G,shape,add_mul,mul_assoc]
    simp only [coeff_add,coeff_C_mul,coeff_X_mul]
  have at2 : a*F.coeff 1+b*F.coeff 2=4620 := by
    rw [←j2,fac,mul_comm F G,shape,add_mul,mul_assoc]
    simp only [coeff_add,coeff_C_mul,coeff_X_mul]
  have d1 : (3:ℤ)∣a*F.coeff 1 := by
    have h := dvd_sub (by decide : (3:ℤ)∣4620) (dvd_mul_of_dvd_left bd (F.coeff 2))
    rwa [←at2,add_sub_cancel_right] at h
  have f1 : (3:ℤ)∣F.coeff 1 :=
    (Int.Prime.dvd_mul' (p:=3) (by decide) d1).resolve_left aNot
  have b1 : (9:ℤ)∣b*F.coeff 1 := by
    change (3:ℤ)*3 ∣ _
    exact mul_dvd_mul bd f1
  have d0 : (9:ℤ)∣a*F.coeff 0 := by
    have h := dvd_sub (by decide : (9:ℤ)∣(-360)) b1
    rwa [←at1,add_sub_cancel_right] at h
  have f0 := cancel_three_squared aNot d0
  have contra : (27:ℤ)∣b*F.coeff 0 := by
    change (3:ℤ)*9 ∣ _
    exact mul_dvd_mul bd f0
  rw [at0] at contra
  exact (by decide : ¬(27:ℤ)∣9) contra

private theorem degree_one_of_mod11_survival {F G : ℤ[X]} (fac : integralPolynomial=F*G)
    (hF : ¬(11:ℤ)∣F.leadingCoeff) : F.natDegree≤1 := by
  have mapProd : integralPolynomial.map z11=(F.map z11)*(G.map z11) := by
    rw [fac,Polynomial.map_mul]
  have wholeLive : integralPolynomial.map z11≠0 := by
    intro h
    have zero0 := congrArg (fun P : (ZMod 11)[X] => P.coeff 0) h
    have nine : (9:ZMod 11)≠0 := by decide
    apply nine
    simpa only [mod11_shape,coeff_zero_eq_eval_zero,eval_add,eval_mul,eval_C,eval_X,
      mul_zero,add_zero,eval_zero] using zero0
  have fLive : F.map z11≠0 := fun z => wholeLive (by rw [mapProd,z,zero_mul])
  have gLive : G.map z11≠0 := fun z => wholeLive (by rw [mapProd,z,mul_zero])
  have fc : z11 F.leadingCoeff≠0 := fun z =>
    hF ((ZMod.intCast_zmod_eq_zero_iff_dvd F.leadingCoeff 11).mp z)
  have dLe : (integralPolynomial.map z11).natDegree≤1 := by
    rw [mod11_shape]
    exact natDegree_add_le_of_le (p:=C (9 : ZMod 11)) (q:=C (3 : ZMod 11)*X)
      (by rw [natDegree_C]) ((natDegree_C_mul_le (3 : ZMod 11) X).trans natDegree_X.le)
  rw [mapProd,natDegree_mul fLive gLive,natDegree_map_of_leadingCoeff_ne_zero z11 fc] at dLe
  omega

private theorem unit_of_mod11_survival {F G : ℤ[X]} (fac : integralPolynomial=F*G)
    (hF : ¬(11:ℤ)∣F.leadingCoeff) : IsUnit F := by
  have d := degree_one_of_mod11_survival fac hF
  by_cases dz : F.natDegree=0
  · have fc := eq_C_of_natDegree_eq_zero dz
    have div : C (F.coeff 0) ∣ integralPolynomial := ⟨G,fac.trans (congrArg (fun P : ℤ[X] => P*G) fc)⟩
    exact fc.symm ▸ isUnit_C.mpr (isPrimitive_iff_isUnit_of_C_dvd.mp integral_primitive _ div)
  · exact False.elim (no_linear_factor (fac.trans (mul_comm F G)) (by omega))

theorem integral_irreducible : Irreducible integralPolynomial := by
  refine ⟨?_,?_⟩
  · intro u
    have d := natDegree_eq_zero_of_isUnit u
    rw [integral_degree] at d
    omega
  · intro F G fac
    have hLead : F.leadingCoeff*G.leadingCoeff=24310 := by
      rw [←leadingCoeff_mul,←fac,integral_lead]
    by_cases hF : (11:ℤ)∣F.leadingCoeff
    · have nG : ¬(11:ℤ)∣G.leadingCoeff := by
        intro hG
        have z : (121:ℤ)∣F.leadingCoeff*G.leadingCoeff := by
          change (11:ℤ)*11 ∣ _
          exact mul_dvd_mul hF hG
        rw [hLead] at z
        exact (by decide : ¬(121:ℤ)∣24310) z
      exact Or.inr (unit_of_mod11_survival (fac.trans (mul_comm F G)) nG)
    · exact Or.inl (unit_of_mod11_survival fac hF)

def rationalPolynomial : ℚ[X] :=
  C ((24310 : ℚ)⁻¹) * integralPolynomial.map (Int.castRingHom ℚ)

theorem rational_monic : rationalPolynomial.Monic := by
  change rationalPolynomial.leadingCoeff=1
  rw [rationalPolynomial,leadingCoeff_mul,leadingCoeff_C,
    leadingCoeff_map_of_injective (show Function.Injective (Int.castRingHom ℚ) from Int.cast_injective),
    integral_lead]
  norm_num

theorem rational_degree : rationalPolynomial.natDegree=8 := by
  rw [rationalPolynomial,natDegree_C_mul (by norm_num),
    natDegree_map_eq_of_injective (show Function.Injective (Int.castRingHom ℚ) from Int.cast_injective),
    integral_degree]

theorem rational_irreducible : Irreducible rationalPolynomial := by
  unfold rationalPolynomial
  apply (irreducible_isUnit_mul (isUnit_C.mpr
      (isUnit_iff_ne_zero.mpr (by norm_num : (24310:ℚ)⁻¹≠0)))).mpr
  exact (IsPrimitive.Int.irreducible_iff_irreducible_map_cast integral_primitive).mp integral_irreducible

end
end RKCert.ReviewedNative.WeightXEight
