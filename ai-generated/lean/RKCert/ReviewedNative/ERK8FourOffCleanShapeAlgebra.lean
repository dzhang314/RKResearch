module

public import RKCert.ReviewedNative.ERK8FourOffScalar
public import RKCert.ReviewedNative.ERKOrderEightLobattoScalar
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Coefficient shape from the two chronological primitive zeros
Source-only draft. The actual producer supplies the two primitive zeros,
not a square divisibility, a free residual vector, or a row-rank callback.
-/
namespace RKResearch.Certified.Graded.MultiOff.FourOff8CleanShape

open Polynomial
open RKResearch.Certified.Graded.MultiOff.FourOff8Scalar

variable {K : Type*} [Field K] [CharZero K]

noncomputable def tapFactor (h : K) : K[X] := X*(X-C h)
noncomputable def cleanPair (x z : K) : K[X] := (X-C x)*(X-C z)
noncomputable def quartic (h x z : K) : K[X] := tapFactor h * cleanPair x z

structure HeadShapeCoeffs (P : K[X]) (h x z theta k : K) : Prop where
  c0 : P.coeff 0 = (shape h x z theta k).p0
  c1 : P.coeff 1 = (shape h x z theta k).p1
  c2 : P.coeff 2 = (shape h x z theta k).p2

structure NormalizedShape (P : K[X]) (h x z theta k : K) : Prop where
  coeffs : HeadShapeCoeffs P h x z theta k
  scale_ne : k ≠ 0
  ratio : theta*cleanE h x z = k*cleanNumer h x
  nonzero : ShapeNonzero (shape h x z theta k) h x z

omit [CharZero K] in
/-- Reuse the checked scalar evaluation for the actual fitted polynomial. -/
theorem HeadShapeCoeffs.eval {P : K[X]} {h x z theta k : K}
    (co : HeadShapeCoeffs P h x z theta k) (hd : P.natDegree ≤ 2) (u : K) :
    P.eval u=(shape h x z theta k).eval u := by
  conv_lhs => rw [LobattoEight.quadratic_coeff_expand P hd]
  simp only [eval_add,eval_monomial,pow_zero,pow_one,mul_one,co.c0,co.c1,co.c2,Quad.eval]

omit [CharZero K] in
/-- The degree cap is exact after normalization; this goes downstream, not upstream. -/
theorem NormalizedShape.head_degree {P : K[X]} {h x z theta k : K}
    (S : NormalizedShape P h x z theta k) (hd : P.natDegree ≤ 2) : P.natDegree=2 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero hd
  rw [S.coeffs.c2]
  exact S.nonzero.p2_ne

omit [CharZero K] in
theorem tapFactor_degree_le (h : K) : (tapFactor h).natDegree ≤ 2 :=
  natDegree_mul_le_of_le (show (X:K[X]).natDegree ≤ 1 by simp) (natDegree_X_sub_C_le h)

omit [CharZero K] in
theorem cleanPair_degree_le (x z : K) : (cleanPair x z).natDegree ≤ 2 :=
  natDegree_mul_le_of_le (natDegree_X_sub_C_le x) (natDegree_X_sub_C_le z)

omit [CharZero K] in
theorem quartic_degree_le (h x z : K) : (quartic h x z).natDegree ≤ 4 :=
  natDegree_mul_le_of_le (tapFactor_degree_le h) (cleanPair_degree_le x z)

private theorem clock_ne_zero {u : K} (root : lobattoNumer u = 0) : u ≠ 0 := by
  intro hu
  rw [hu] at root
  norm_num [lobattoNumer] at root

private theorem cleanPair_monomials (x z : K) : cleanPair x z =
    monomial 0 (x*z) + monomial 1 (-(x+z)) + monomial 2 1 := by
  simp only [cleanPair, ← C_mul_X_pow_eq_monomial, map_neg,map_add,map_mul,
    pow_zero,pow_one,mul_one,map_one,one_mul]
  ring

private theorem tap_primitive_eval (P : K[X]) (hd : P.natDegree ≤ 2) (h u : K) :
    (primitive (tapFactor h*P)).eval u =
       P.coeff 0*(u^3/3-h*u^2/2)+P.coeff 1*(u^4/4-h*u^3/3)+P.coeff 2*(u^5/5-h*u^4/4) := by
  conv_lhs => rw [LobattoEight.quadratic_coeff_expand P hd]
  simp only [tapFactor,mul_assoc,sub_mul,mul_sub,mul_add,X_mul_monomial,C_mul_monomial,
    map_add,map_sub,primitive_monomial,eval_add,eval_sub,eval_monomial]
  norm_num <;> ring

/-- Two separated primitive tests force the quadratic coefficients directly.
No roots of P and no polynomial multiplicity API enter the proof. -/
private theorem kernel_of_tap_zeros (P : K[X]) (hd : P.natDegree ≤ 2)
    {h x : K} (h0 : h ≠ 0) (x0 : x ≠ 0) (xh : x ≠ h)
    (Hh : (primitive (tapFactor h*P)).eval h = 0)
    (Hx : (primitive (tapFactor h*P)).eval x = 0) :
    ∃ k, P.coeff 0=2*k*h*x ∧ P.coeff 1=-(4*x+3*h)*k ∧ P.coeff 2=5*k := by
  let a := P.coeff 0
  let b := P.coeff 1
  let c := P.coeff 2
  have Eh := (tap_primitive_eval P hd h h).symm.trans Hh
  have Ex := (tap_primitive_eval P hd h x).symm.trans Hx
  change a*(h^3/3-h*h^2/2)+b*(h^4/4-h*h^3/3)+c*(h^5/5-h*h^4/4)=0 at Eh
  change a*(x^3/3-h*x^2/2)+b*(x^4/4-h*x^3/3)+c*(x^5/5-h*x^4/4)=0 at Ex
  have eh : h^3*(10*a+5*h*b+3*h^2*c)=0 := by linear_combination -60*Eh
  have dh := (mul_eq_zero.mp eh).resolve_left (pow_ne_zero 3 h0)
  have ex : x^2*((x-h)^2*(5*b+(4*x+3*h)*c))=0 := by
    linear_combination 20*Ex-2*x^2*(x/3-h/2)*dh
  have dx := (mul_eq_zero.mp ((mul_eq_zero.mp ex).resolve_left (pow_ne_zero 2 x0))).resolve_left
    (pow_ne_zero 2 (sub_ne_zero.mpr xh))
  let k := c/5
  change ∃ k, a=2*k*h*x ∧ b=-(4*x+3*h)*k ∧ c=5*k
  refine ⟨k,?_,?_,?_⟩
  · dsimp only [k]
    linear_combination (1/10:K)*dh-(h/10)*dx
  · dsimp only [k]
    linear_combination (1/5:K)*dx
  · dsimp only [k]
    ring

/-- Shape before fixing the scale ratio. The same theta occurs at h and x. -/
theorem coefficients_of_clean_tap (P : K[X]) (hd : P.natDegree ≤ 2)
    {h x z theta : K} (D : CleanClocks h x z)
    (Hh : (primitive (tapFactor h*P)).eval h = theta*(primitive (quartic h x z)).eval h)
    (Hx : (primitive (tapFactor h*P)).eval x = theta*(primitive (quartic h x z)).eval x) :
    ∃ k, HeadShapeCoeffs P h x z theta k := by
  let R := P-C theta*cleanPair x z
  have dPair : (C theta*cleanPair x z).natDegree ≤ 2 :=
    (natDegree_C_mul_le theta _).trans (cleanPair_degree_le x z)
  have dR : R.natDegree ≤ 2 := (natDegree_sub_le_iff_left dPair).mpr hd
  have poly : tapFactor h * R = tapFactor h*P-C theta*quartic h x z := by
    dsimp only [R,quartic]
    ring
  have prim (u : K) : (primitive (tapFactor h*R)).eval u =
      (primitive (tapFactor h*P)).eval u-theta*(primitive (quartic h x z)).eval u := by
    have scal : (primitive (C theta*quartic h x z)).eval u =
        theta*(primitive (quartic h x z)).eval u := by
      rw [←smul_eq_C_mul,map_smul,eval_smul,smul_eq_mul]
    rw [poly,map_sub,eval_sub,scal]
  have zero_h : (primitive (tapFactor h*R)).eval h = 0 := by rw [prim,Hh,sub_self]
  have zero_x : (primitive (tapFactor h*R)).eval x = 0 := by rw [prim,Hx,sub_self]
  obtain ⟨k,u0,u1,u2⟩ := kernel_of_tap_zeros R dR (clock_ne_zero D.root_h)
    (clock_ne_zero D.root_x) D.h_ne_x.symm zero_h zero_x
  have r0 : R.coeff 0 = P.coeff 0-theta*(x*z) := by
    simp [R,cleanPair_monomials,coeff_C_mul,coeff_monomial]
  have r1 : R.coeff 1 = P.coeff 1+theta*(x+z) := by
    simp [R,cleanPair_monomials,coeff_C_mul,coeff_monomial,sub_neg_eq_add] <;> ring
  have r2 : R.coeff 2 = P.coeff 2-theta := by
    simp [R,cleanPair_monomials,coeff_C_mul,coeff_monomial]
  rw [r0] at u0
  rw [r1] at u1
  rw [r2] at u2
  refine ⟨k,?_,?_,?_⟩
  · simp only [shape]; linear_combination u0
  · simp only [shape]; linear_combination u1
  · simp only [shape]; linear_combination u2

/-- Shared scale and ratio from the first-clean XP primitive, not a branch hypothesis. -/
theorem normalize_head_of_primitive {P : K[X]} {h x z theta k : K}
    (D : CleanClocks h x z) (hd : P.natDegree ≤ 2) (hnz : P ≠ 0)
    (co : HeadShapeCoeffs P h x z theta k) (H : (primitive (X*P)).eval h=0) :
    NormalizedShape P h x z theta k := by
  have H0 := H
  rw [LobattoEight.primitive_eval_X_quadratic P hd,co.c0,co.c1,co.c2] at H0
  have hz : h^2*(theta*cleanE h x z-k*cleanNumer h x)=0 := by
    simp only [shape] at H0
    unfold cleanE cleanNumer
    linear_combination 12*H0
  have hs : theta*cleanE h x z = k*cleanNumer h x :=
    sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (pow_ne_zero 2 (clock_ne_zero D.root_h)))
  have hk : k ≠ 0 := by
    intro kz
    have tz0 : theta*cleanE h x z=0 := by simpa only [kz,zero_mul] using hs
    have tz : theta=0 := (mul_eq_zero.mp tz0).resolve_right (cleanE_ne_zero D)
    have z0 : P.coeff 0 = 0 := by simpa [shape,kz,tz] using co.c0
    have z1 : P.coeff 1 = 0 := by simpa [shape,kz,tz] using co.c1
    have z2 : P.coeff 2 = 0 := by simpa [shape,kz,tz] using co.c2
    apply hnz
    rw [LobattoEight.quadratic_coeff_expand P hd,z0,z1,z2]
    simp
  exact ⟨co,hk,hs,shape_nonzero_of_clean D hk hs⟩

end RKResearch.Certified.Graded.MultiOff.FourOff8CleanShape
