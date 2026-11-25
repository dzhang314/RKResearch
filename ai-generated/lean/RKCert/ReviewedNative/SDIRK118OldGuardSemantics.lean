module

public import RKCert.ReviewedNative.SDIRK118ScalarExistence

import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

noncomputable section

namespace RKResearch.Certified.PaidDefectBridge.SDIRK118.OldGuardSemantics

open ClaimPin ScalarBindings ScalarQuadrature ScalarExistence
open Polynomial
open scoped BigOperators Matrix Polynomial

local notation "ℙ" => Polynomial ℝ

def z2 (s : ℝ) : ℝ := 1 + 3*s
def w (s t : ℝ) (i : Fin 4) : ℝ := 2*uAt s t i
def rawR (s t : ℝ) (i : Fin 4) : ℙ :=
  ∏ j ∈ (Finset.univ : Finset (Fin 4)).erase i, linearFactor (uAt s t j)

def normR (s t : ℝ) (i : Fin 4) : ℙ :=
  (8 : ℝ) • ((rawR s t i).comp (zAt s • X))

def normZ (s t : ℝ) : ℙ := (16 : ℝ) • ((Zpoly s t).comp (zAt s • X))
def normLine (s t : ℝ) (i : Fin 4) : ℙ := z2 s • X - C (w s t i)

theorem z2_twice (s : ℝ) : z2 s = 2*zAt s := by
  unfold z2 zAt aAt
  ring

private theorem raw_all (s t : ℝ) :
    (∏ i : Fin 4, linearFactor (uAt s t i)) = Zpoly s t := by
  simp [uAt,Zpoly,Jpoly,cubic,Fin.prod_univ_succ] <;> ring

private theorem raw_factor (s t : ℝ) (i : Fin 4) :
    Zpoly s t = linearFactor (uAt s t i) * rawR s t i := by
  rw [← raw_all s t]
  exact (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm

theorem line_scale (s t : ℝ) (i : Fin 4) :
    normLine s t i = (2 : ℝ) • ((linearFactor (uAt s t i)).comp (zAt s • X)) := by
  rw [normLine,linearFactor,sub_comp,X_comp,C_comp,smul_sub,smul_smul,z2_twice,w,
    smul_eq_C_mul (p := C (uAt s t i)),map_mul]

theorem norm_factor (s t : ℝ) (i : Fin 4) :
    normZ s t = normLine s t i * normR s t i := by
  rw [normZ,normR,line_scale,raw_factor s t i,mul_comp,smul_mul_smul_comm]
  norm_num

def p (M : MonomialBasis) (s t : ℝ) (i : Fin 4) (j : ℕ) : ℝ :=
  840 * mean M (X^j * normR s t i)
def m (M : MonomialBasis) (s t : ℝ) (j : ℕ) : ℝ :=
  840 * mean M (X^j * normZ s t)

theorem moment_step (M : MonomialBasis) (s t : ℝ) (i : Fin 4) (j : ℕ) :
    m M s t j = z2 s * p M s t i (j+1) - w s t i * p M s t i j := by
  have e : (X^j : ℙ)*(normLine s t i*normR s t i) =
      z2 s • (X^(j+1)*normR s t i)-w s t i • (X^j*normR s t i) := by
    simp only [normLine,smul_eq_C_mul,pow_succ]
    ring
  rw [m,norm_factor s t i,e,map_sub,map_smul,map_smul]
  simp only [smul_eq_mul,p]
  ring

theorem mu_scale (M : MonomialBasis) (hm : standardPowers M) (s t : ℝ)
    (hz : zAt s ≠ 0) (j : ℕ) :
    μ M s t j = (zAt s)^j * m M s t j / (840*16) := by
  unfold μ
  rw [← mean_scale M hm (zAt s) hz,mul_comp,X_pow_comp,smul_pow,smul_mul_assoc,map_smul]
  simp only [smul_eq_mul,m,normZ,mul_smul_comm,map_smul]
  ring

def D' (M : MonomialBasis) (s t : ℝ) : ℝ := m M s t 0*m M s t 2-(m M s t 1)^2
def N1 (M : MonomialBasis) (s t : ℝ) : ℝ := m M s t 1*m M s t 2-m M s t 0*m M s t 3
def N0 (M : MonomialBasis) (s t : ℝ) : ℝ := m M s t 1*m M s t 3-(m M s t 2)^2
def clearedUnit (M : MonomialBasis) (s t : ℝ) : ℙ :=
  C (D' M s t)*X^2 + C (N1 M s t)*X + C (N0 M s t)

theorem determinant_scale (M : MonomialBasis) (hm : standardPowers M) (s t : ℝ)
    (hz : zAt s ≠ 0) :
    momentDet M s t = (zAt s)^2 * (D' M s t) / ((840*16)^2) := by
  simp only [momentDet,mu_scale M hm s t hz,D']
  ring

theorem D'_pos (M : MonomialBasis) (hm : standardPowers M) (s t : ℝ)
    (hz : 0 < zAt s) (hD : 0 < momentDet M s t) : 0 < D' M s t := by
  rw [determinant_scale M hm s t hz.ne'] at hD
  have hh : 0 < (zAt s)^2 * D' M s t := by
    exact (div_pos_iff_of_pos_right (by norm_num)).mp hD
  exact pos_of_mul_pos_right hh (sq_nonneg _)

theorem Bstar_scaling (M : MonomialBasis) (hm : standardPowers M) (s t : ℝ)
    (hz : 0 < zAt s) (hD : 0 < momentDet M s t) :
    (D' M s t) • ((Bstar M s t).comp (zAt s • X)) =
      (zAt s)^2 • clearedUnit M s t := by
  have hP := (D'_pos M hm s t hz hD).ne'
  have h1 : D' M s t * beta1 M s t = zAt s * N1 M s t := by
    simp only [beta1,mu_scale M hm s t hz.ne',determinant_scale M hm s t hz.ne',N1]
    field_simp [hz.ne',hP] <;> ring
  have h0 : D' M s t * beta0 M s t = (zAt s)^2 * N0 M s t := by
    simp only [beta0,mu_scale M hm s t hz.ne',determinant_scale M hm s t hz.ne',N0]
    field_simp [hz.ne',hP] <;> ring
  apply Polynomial.funext
  intro Y
  simp only [Polynomial.eval_smul,smul_eq_mul,eval_comp,eval_X,Bstar,clearedUnit,
    eval_add,eval_mul,Polynomial.eval_pow,eval_C]
  linear_combination (zAt s*Y)*h1+h0

def dotRow (M : MonomialBasis) (s t : ℝ) (a0 a1 a2 : ℝ) : ℝ :=
  a0*N0 M s t+a1*N1 M s t+a2*D' M s t

theorem dotRow_mean (M : MonomialBasis) (s t k : ℝ) (P : ℙ) :
    dotRow M s t (k*mean M P) (k*mean M (X*P)) (k*mean M (X^2*P)) =
      k * mean M (P * clearedUnit M s t) := by
  have e : P*clearedUnit M s t = (N0 M s t) • P +
      (N1 M s t) • (X*P) + (D' M s t) • (X^2*P) := by
    simp only [clearedUnit,smul_eq_C_mul]
    ring
  rw [e]
  simp only [dotRow,map_add,map_smul,smul_eq_mul]
  ring

def hankel (a0 a1 a2 a3 a4 : ℝ) : ℝ :=
  a0*(a2*a4-a3^2)-a1*(a1*a4-a2*a3)+a2*(a1*a3-a2^2)

def G (M : MonomialBasis) (s t : ℝ) (i : Fin 4) : ℝ :=
  hankel (p M s t i 0) (p M s t i 1) (p M s t i 2) (p M s t i 3) (p M s t i 4)

theorem hankel_scale (M : MonomialBasis) (s t : ℝ) (i : Fin 4) :
    dotRow M s t (p M s t i 0) (p M s t i 1) (p M s t i 2) =
      (z2 s)^2 * G M s t i := by
  simp only [dotRow,N0,N1,D',G,hankel]
  rw [moment_step M s t i 0,moment_step M s t i 1,moment_step M s t i 2,
    moment_step M s t i 3]
  ring

/-- Cross-multiplied version of the saved Omega scaling. Every factor
other than the guard is explicit, and the only moment sign is hD. -/
theorem omega_scale (M : MonomialBasis) (hm : standardPowers M) (s t : ℝ) (i : Fin 4)
    (hz : 0 < zAt s) (hD : 0 < momentDet M s t) :
    (zAt s)^2 * ((z2 s)^2 * G M s t i) = 840*8*(D' M s t)*omegaOld M s t i := by
  have hω : mean M ((Bstar M s t*rawR s t i).comp (zAt s • X)) = omegaOld M s t i :=
    mean_scale M hm (zAt s) hz.ne' _
  have ep : (zAt s)^2 • (normR s t i * clearedUnit M s t) =
      (8*D' M s t) • ((Bstar M s t*rawR s t i).comp (zAt s • X)) := by
    rw [← mul_smul_comm,← Bstar_scaling M hm s t hz hD,normR,smul_mul_smul_comm,mul_comp]
    congr 1
    exact mul_comm _ _
  have em := congrArg (fun P : ℙ => mean M P) ep
  change mean M ((zAt s)^2 • _) = mean M ((8*D' M s t) • _) at em
  simp only [map_smul,smul_eq_mul,hω] at em
  have eg := hankel_scale M s t i
  have ef := dotRow_mean M s t 840 (normR s t i)
  have e0 : p M s t i 0 = 840 * mean M (normR s t i) := by simp [p]
  have e1 : p M s t i 1 = 840 * mean M (X*normR s t i) := by simp [p]
  rw [e0,e1] at eg
  change dotRow M s t (840*mean M (normR s t i))
    (840*mean M (X*normR s t i)) (840*mean M (X^2 * normR s t i)) = _ at eg
  rw [ef] at eg
  rw [←eg]
  linear_combination 840*em

/-- Omitted-node order from the archived p-row builder. -/
def kept : Fin 4 → Fin 3 → Fin 4 :=
  ![![1,2,3],![0,2,3],![0,1,3],![0,1,2]]

private theorem rawR_three (s t : ℝ) (i : Fin 4) :
    rawR s t i = linearFactor (uAt s t (kept i 0)) *
      linearFactor (uAt s t (kept i 1)) * linearFactor (uAt s t (kept i 2)) := by
  have e : (Finset.univ : Finset (Fin 4)).erase i = {kept i 0,kept i 1,kept i 2} := by
    fin_cases i <;> decide
  have e01 : kept i 0 ≠ kept i 1 := by fin_cases i <;> decide
  have e02 : kept i 0 ≠ kept i 2 := by fin_cases i <;> decide
  have e12 : kept i 1 ≠ kept i 2 := by fin_cases i <;> decide
  rw [rawR,e,Finset.prod_insert (by simp [e01,e02]),Finset.prod_pair e12]
  ring

theorem normR_three (s t : ℝ) (i : Fin 4) :
    normR s t i =
      normLine s t (kept i 0)*normLine s t (kept i 1)*normLine s t (kept i 2) := by
  rw [normR,rawR_three,mul_comp,mul_comp,line_scale,line_scale,line_scale,
    smul_mul_smul_comm,smul_mul_smul_comm]
  norm_num

/-- Closed expression for the archived four-term p-row. For j≤4 the
numerator 840 clears each displayed denominator 1 through 8. -/
def pExpr (s t : ℝ) (i : Fin 4) (j : ℕ) : ℝ :=
  let A := w s t (kept i 0)
  let B := w s t (kept i 1)
  let C := w s t (kept i 2)
  let z := z2 s
  840*((-(A*B*C))/((j+1:ℕ):ℝ) + (z*(A*B+A*C+B*C))/((j+2:ℕ):ℝ) +
    (-(z^2*(A+B+C)))/((j+3:ℕ):ℝ) + z^3/((j+4:ℕ):ℝ))

theorem p_expr_exact (M : MonomialBasis) (hm : standardPowers M)
    (s t : ℝ) (i : Fin 4) (j : ℕ) : p M s t i j = pExpr s t i j := by
  let A := w s t (kept i 0)
  let B := w s t (kept i 1)
  let D := w s t (kept i 2)
  let z := z2 s
  let c0 := -(A*B*D)
  let c1 := z*(A*B+A*D+B*D)
  let c2 := -(z^2*(A+B+D))
  let c3 := z^3
  have R : normR s t i =
      c0 • (X^0 : ℙ) + c1 • X^1 + c2 • X^2 + c3 • X^3 := by
    rw [normR_three]
    change (z • X - C A)*(z • X - C B)*(z • X - C D) = _
    simp only [smul_eq_C_mul,c0,c1,c2,c3,map_neg,map_mul,map_add,map_pow]
    ring
  have shift (k : ℕ) (a : ℝ) : (X^j : ℙ)*(a • X^k) = a • X^(j+k) := by
    rw [mul_smul_comm,← pow_add]
  rw [p,R]
  simp only [mul_add,shift,map_add,map_smul,smul_eq_mul,mean_pow M hm]
  simp only [pExpr,div_eq_mul_inv,A,B,D,z,c0,c1,c2,c3,Nat.add_zero]
  ring

def mExpr (s t : ℝ) (j : ℕ) : ℝ :=
  z2 s*pExpr s t 1 (j+1)-w s t 1*pExpr s t 1 j

def omegaExpr (s t : ℝ) (i : Fin 4) : ℝ :=
  hankel (pExpr s t i 0) (pExpr s t i 1) (pExpr s t i 2) (pExpr s t i 3) (pExpr s t i 4)

def aExpr (s t : ℝ) (j : ℕ) : ℝ :=
  12 * ((z2 s / ((j+2:ℕ):ℝ))*(pExpr s t 1 0-pExpr s t 1 (j+2)) -
    (w s t 1 / ((j+1:ℕ):ℝ))*(pExpr s t 1 0-pExpr s t 1 (j+1)))

def jExpr (s t : ℝ) : ℝ :=
  let m := mExpr s t
  aExpr s t 0*(m 1*m 3-(m 2)^2)+aExpr s t 1*(m 1*m 2-m 0*m 3)+
    aExpr s t 2*(m 0*m 2-(m 1)^2)

theorem G_eq_receipt (M : MonomialBasis) (hm : standardPowers M) (s t : ℝ) (i : Fin 4) :
    G M s t i = omegaExpr s t i := by
  simp only [G,omegaExpr,p_expr_exact M hm]



private theorem primitive_scale (M : MonomialBasis) (hm : standardPowers M) (z : ℝ) (P : ℙ) :
    (coefficientPrimitive M P).comp (z • X) =
      z • coefficientPrimitive M (P.comp (z • X)) := by
  let F := (coefficientPrimitive M P).comp (z • X) -
    z • coefficientPrimitive M (P.comp (z • X))
  have hd : F.derivative = 0 := by
    simp only [F,derivative_sub,derivative_comp,derivative_smul,derivative_X,
      derivative_primitive M hm,smul_mul_assoc,one_mul,sub_self]
  have hz : F.eval 0 = 0 := by
    simp [F,eval_sub,eval_comp,Polynomial.eval_smul,eval_X,primitive_eval_zero M hm]
  have e := eq_C_of_derivative_eq_zero hd
  rw [(coeff_zero_eq_eval_zero F).trans hz,map_zero] at e
  exact sub_eq_zero.mp e

private theorem mean_primitive_monomial (M : MonomialBasis) (hm : standardPowers M)
    (R : ℙ) (j : ℕ) :
    (((j+1 : ℕ) : ℝ)) * mean M (X^j*coefficientPrimitive M R) =
      mean M R - mean M (X^(j+1)*R) := by
  let IR := coefficientPrimitive M R
  let F := (X^(j+1) : ℙ)*IR
  have hnat : (j:ℝ)+1 = ((j+1:ℕ):ℝ) := by simp
  have e : F.derivative =
      (((j+1:ℕ):ℝ)) • (X^j*IR) + X^(j+1)*R := by
    dsimp only [F]
    rw [derivative_mul,derivative_X_pow_succ,derivative_primitive M hm,hnat,smul_eq_C_mul,mul_assoc]
  have ev0 : F.eval 0=0 := by
    simp only [F,IR,eval_mul,primitive_eval_zero M hm,mul_zero]
  have ev1 : F.eval 1=mean M R := by
    simp only [F,eval_mul,Polynomial.eval_pow,eval_X,one_pow,one_mul,IR,mean_eq_eval_primitive M hm]
  have h := mean_derivative M hm F
  rw [e,ev0,ev1,map_add,map_smul,smul_eq_mul,sub_zero] at h
  linear_combination h

def residualRow (M : MonomialBasis) (s t : ℝ) (j : ℕ) : ℝ :=
  12 * ((z2 s / ((j+2:ℕ):ℝ))*(p M s t 1 0-p M s t 1 (j+2)) -
    (w s t 1 / ((j+1:ℕ):ℝ))*(p M s t 1 0-p M s t 1 (j+1)))

theorem residualRow_mean (M : MonomialBasis) (hm : standardPowers M) (s t : ℝ) (j : ℕ) :
    residualRow M s t j =
      (12*840) * mean M (X^j * (normLine s t 1 * coefficientPrimitive M (normR s t 1))) := by
  let R := normR s t 1
  let IR := coefficientPrimitive M R
  have ep (k : ℕ) : p M s t 1 0-p M s t 1 (k+1) =
      840 * (((k+1:ℕ):ℝ))*mean M (X^k*IR) := by
    have h := mean_primitive_monomial M hm R k
    simp only [p,pow_zero,one_mul]
    change 840*mean M R-840*mean M (X^(k+1)*R)=_
    linear_combination -(840:ℝ)*h
  have e : (X^j : ℙ)*(normLine s t 1*IR) =
      z2 s • (X^(j+1)*IR)-w s t 1 • (X^j*IR) := by
    simp only [normLine,smul_eq_C_mul,pow_succ]
    ring
  have n1 : ((j+1:ℕ):ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero j)
  have n2 : ((j+2:ℕ):ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero (j+1))
  unfold residualRow
  rw [show j+2=(j+1)+1 by rfl,ep (j+1),ep j]
  change _ = (12*840)*mean M ((X^j)*(normLine s t 1*IR))
  rw [e,map_sub,map_smul,map_smul,smul_eq_mul,smul_eq_mul]
  field_simp [n1,n2] <;> ring

def GJ (M : MonomialBasis) (s t : ℝ) : ℝ :=
  dotRow M s t (residualRow M s t 0) (residualRow M s t 1) (residualRow M s t 2)

theorem GJ_eq_receipt (M : MonomialBasis) (hm : standardPowers M) (s t : ℝ) :
    GJ M s t = jExpr s t := by
  simp only [GJ,dotRow,residualRow,N0,N1,D',jExpr,aExpr,mExpr,
    moment_step M s t 1,p_expr_exact M hm]

theorem residualGuard_mean (M : MonomialBasis) (hm : standardPowers M) (s t : ℝ) :
    GJ M s t = (12*840)*mean M
      ((normLine s t 1 * coefficientPrimitive M (normR s t 1))*clearedUnit M s t) := by
  simp only [GJ,residualRow_mean M hm,pow_zero,pow_one,one_mul]
  exact dotRow_mean M s t (12*840) (normLine s t 1*coefficientPrimitive M (normR s t 1))

private theorem rawR_one (s t : ℝ) : rawR s t 1 = Jpoly s t := by
  rw [rawR_three s t 1]
  change linearFactor (1:ℝ)*linearFactor s*linearFactor t = Jpoly s t
  unfold Jpoly cubic
  ring

theorem residual_scale (M : MonomialBasis) (hm : standardPowers M) (s t : ℝ)
    (hz : 0 < zAt s) (hD : 0 < momentDet M s t) :
    (zAt s)^3 * GJ M s t = (12*840*16)*(D' M s t)*residualJ0 M s t := by
  let z := zAt s
  let B := Bstar M s t
  let Q := clearedUnit M s t
  let a := aAt s
  let J := Jpoly s t
  let IR := coefficientPrimitive M (normR s t 1)
  let IJ := coefficientPrimitive M J
  let L := normLine s t 1
  have rscale : z • IR = (8:ℝ) • (IJ.comp (z • X)) := by
    change z • coefficientPrimitive M (normR s t 1) = _
    rw [normR,rawR_one,map_smul,primitive_scale M hm,smul_smul,smul_smul]
    congr 1
    ring
  have Lscale : L = (2:ℝ) • ((linearFactor a).comp (z•X)) :=
    line_scale s t 1
  have escale : z^3 • ((L*IR)*Q) =
      ((16:ℝ)*D' M s t) • (((linearFactor a)*B*IJ).comp (z•X)) := by
    calc
      _ = (L*(z • IR))*(z^2 • Q) := by
        simp only [smul_eq_C_mul,pow_succ,map_mul]
        ring
      _ = _ := by
        have hB : z^2 • Q = (D' M s t) • (B.comp (z • X)) :=
          (Bstar_scaling M hm s t hz hD).symm
        rw [rscale,Lscale,hB]
        simp only [smul_mul_smul_comm, mul_comp, show (2 : ℝ) * 8 = 16 by norm_num]
        congr 1 <;> ac_rfl
  have hj : mean M (((linearFactor a)*B*IJ).comp (z•X)) = residualJ0 M s t :=
    mean_scale M hm z hz.ne' _
  have em := congrArg (fun P : ℙ => mean M P) escale
  change mean M (z^3 • ((L*IR)*Q)) =
    mean M (((16:ℝ)*D' M s t) • (((linearFactor a)*B*IJ).comp (z•X))) at em
  simp only [map_smul,smul_eq_mul,hj] at em
  change z^3*GJ M s t = _
  rw [residualGuard_mean M hm]
  change z^3*((12*840)*mean M ((L*IR)*Q)) = _
  linear_combination (12*840:ℝ)*em

end RKResearch.Certified.PaidDefectBridge.SDIRK118.OldGuardSemantics
