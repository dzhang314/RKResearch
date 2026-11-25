module

public import RKCert.ReviewedNative.SDIRK118ScalarAffineResponse
public import RKCert.ReviewedNative.SDIRK118ConditionalFin11
public import RKCert.ReviewedNative.SDIRK118ForwardCubics

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

noncomputable section

namespace RKResearch.Certified.PaidDefectBridge.SDIRK118.ScalarCalibration

open RKResearch
open RKResearch.Certified.PaidDefectBridge.ForwardChart (tiltA tiltB)
open RKResearch.Certified.PaidDefectBridge.SDIRK118 (PolyBound wDot)
open RKResearch.Certified.PaidDefectBridge.SDIRK118.ClaimPin
open RKResearch.Certified.PaidDefectBridge.SDIRK118.LiteralAssembly (Geometry)
open RKResearch.Certified.PaidDefectBridge.SDIRK118.ScalarBindings
open RKResearch.Certified.PaidDefectBridge.SDIRK118.ScalarQuadrature
open RKResearch.Certified.PaidDefectBridge.SDIRK118.ScalarMasses
open RKResearch.Certified.PaidDefectBridge.SDIRK118.ScalarAffineResponse
open Polynomial
open scoped Matrix Polynomial BigOperators

local notation "ℙ" => Polynomial ℝ

private def rawMean (M : MonomialBasis) (z : ℝ) : ℙ →ₗ[ℝ] ℝ :=
  z⁻¹ • ((evalAt M z).comp (coefficientPrimitive M))

private theorem rawMean_apply (M : MonomialBasis) (z : ℝ) (P : ℙ) :
    rawMean M z P = avg M z P := by
  change z⁻¹ * evalAt M z (coefficientPrimitive M P) =
    evalAt M z (coefficientPrimitive M P) / z
  rw [div_eq_mul_inv, mul_comm]

private theorem pMul (n m : ℕ) (P Q : ℙ)
    (hp : PolyBound n P) (hq : PolyBound m Q) : PolyBound (n+m) (P * Q) :=
  natDegree_le_iff_coeff_eq_zero.mp
    (natDegree_mul_le.trans (Nat.add_le_add (natDegree_le_iff_coeff_eq_zero.mpr hp)
      (natDegree_le_iff_coeff_eq_zero.mpr hq)))

private theorem pUpper {n m : ℕ} {P : ℙ} (h : n ≤ m) (hp : PolyBound n P) : PolyBound m P :=
  fun i hi => hp i (h.trans_lt hi)

private theorem pSub {n : ℕ} {P Q : ℙ} (hp : PolyBound n P) (hq : PolyBound n Q) :
    PolyBound n (P - Q) :=
  natDegree_le_iff_coeff_eq_zero.mp
    ((natDegree_sub_le P Q).trans (max_le (natDegree_le_iff_coeff_eq_zero.mpr hp)
      (natDegree_le_iff_coeff_eq_zero.mpr hq)))

private theorem pFactor (x : ℝ) : PolyBound 1 (linearFactor x) :=
  natDegree_le_iff_coeff_eq_zero.mp ((natDegree_X_sub_C x).le)

private theorem pX : PolyBound 1 (X : ℙ) :=
  natDegree_le_iff_coeff_eq_zero.mp (natDegree_X.le)

private theorem pJ (s t : ℝ) : PolyBound 3 (Jpoly s t) :=
  pMul 2 1 _ _ (pMul 1 1 _ _ (pFactor s) (pFactor t)) (pFactor 1)

private theorem pZ (s t : ℝ) : PolyBound 4 (Zpoly s t) :=
  pMul 1 3 _ _ (pFactor (aAt s)) (pJ s t)

private theorem pB (M : MonomialBasis) (s t c : ℝ) (h : quadraticAt M s t c = 0) :
    PolyBound 2 (Bstar M s t) := by
  rw [beta_factor M s t c h]
  exact pMul 1 1 _ _ (pFactor _) (pFactor _)

private theorem affineCompBound (P : ℙ) (γ : ℝ) (n : ℕ)
    (hp : PolyBound n P) : PolyBound n (P.comp (1 - γ • X)) := by
  have hq : ((1 : ℙ) - γ • X).natDegree ≤ 1 := by
    refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · simp
    · simpa only [natDegree_X] using natDegree_smul_le γ (X : ℙ)
  apply natDegree_le_iff_coeff_eq_zero.mp
  exact natDegree_comp_le.trans (by
    simpa only [Nat.mul_one] using Nat.mul_le_mul (natDegree_le_iff_coeff_eq_zero.mpr hp) hq)

/-- Scale the actual coefficient primitive. Differentiate both sides and
use their common constant term zero. -/
private theorem primitive_comp_scale (M : MonomialBasis) (hm : standardPowers M) (γ : ℝ) (P : ℙ) :
    (coefficientPrimitive M P).comp (γ • X) =
      γ • coefficientPrimitive M (P.comp (γ • X)) := by
  let F := (coefficientPrimitive M P).comp (γ • X) -
    γ • coefficientPrimitive M (P.comp (γ • X))
  have hd : F.derivative = 0 := by
    simp only [F, derivative_sub, derivative_comp, derivative_smul, derivative_X,
      derivative_primitive M hm, smul_mul_assoc, one_mul, sub_self]
  have hf : F.eval 0 = 0 := by
    simp [F, eval_sub, eval_comp, Polynomial.eval_smul, eval_X, primitive_eval_zero M hm]
  have hc : F.coeff 0 = 0 := (coeff_zero_eq_eval_zero F).trans hf
  have hh := eq_C_of_derivative_eq_zero hd
  rw [hc, map_zero] at hh
  exact sub_eq_zero.mp hh

/-- The chart's literal first covector in Lambda, represented linearly
without an abstract matrix rank. -/
private def pairLeft (g : Geometry ℝ) (K : ℙ) : ℙ →ₗ[ℝ] ℝ where
  toFun H := g.pairing H K
  map_add' H P := by
    simp only [Geometry.pairing, wDot, map_add, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' a H := by
    simp only [Geometry.pairing, wDot, map_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
    exact Finset.sum_congr rfl (fun i _ => by ring)

private def clean (M : MonomialBasis) (s d : ℝ) : ℙ →ₗ[ℝ] ℝ :=
  let a := aAt s
  let γ := (zAt s)⁻¹
  let gd := gdAt s (etaAt s) d
  (tiltA a d (1/2) gd) • evalAt M γ + (tiltB a d (g1At s) gd) • evalAt M (γ*a) +
    evalAt M (γ*d)

private theorem clean_response (M : MonomialBasis) (hm : standardPowers M)
    (s d : ℝ) (H : ℙ) :
    clean M s d H = response s d (fun T => H.eval ((zAt s)⁻¹ * T)) := by
  simp only [clean,response,LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul,
    evalAt_eq_eval M hm,mul_one]
  ring

private theorem response_scale (s d k : ℝ) (f : ℝ → ℝ) :
    response s d (fun T => k * f T) = k * response s d f := by
  dsimp [response]
  ring

/-- Two-by-two elimination is enough for the actual H4 coefficient.
The nonzero probe is a specified linear combination, not a rank premise. -/
private theorem elimination (rho lam : ℙ →ₗ[ℝ] ℝ) (p0 p1 R H : ℙ)
    (x4 xr e : ℝ) (rDef : R = p1 - x4 • p0)
    (hDef : H = e • p0 - (rho (e • p0) / rho R) • R)
    (lamR : lam R ≠ 0) (probe : rho (p1 - xr • p0) ≠ 0)
    (det : lam p1 * rho p0 - lam p0 * rho p1 = 0) :
    lam H = 0 := by
  have ll : lam R = lam p1 - x4 * lam p0 := by
    rw [rDef, map_sub, map_smul, smul_eq_mul]
  have rr : rho R = rho p1 - x4 * rho p0 := by
    rw [rDef, map_sub, map_smul, smul_eq_mul]
  have row : lam R * rho p0 - lam p0 * rho R = 0 := by
    rw [ll,rr]
    linear_combination det
  have rne : rho R ≠ 0 := by
    intro hr
    have hr0 : rho p0 = 0 := by
      rw [hr, mul_zero, sub_zero] at row
      exact (mul_eq_zero.mp row).resolve_left lamR
    have hr1 : rho p1 = 0 := by
      rw [hr,hr0,mul_zero,sub_zero] at rr
      exact rr.symm
    apply probe
    rw [map_sub,map_smul,smul_eq_mul,hr0,hr1,mul_zero,sub_zero]
  simp only [hDef,map_sub,map_smul,smul_eq_mul]
  apply sub_eq_zero.mpr
  apply mul_right_cancel₀ rne
  rw [mul_right_comm (e * rho p0 / rho R) (lam R) (rho R), div_mul_cancel₀ _ rne]
  linear_combination -e * row

section Literal

variable (M : MonomialBasis) (hm : standardPowers M) (s t c : ℝ)
variable (seed : ExactScalarSeed M s t c)

local notation "𝒢" => geometry M s t c
local notation "γ" => (zAt s)⁻¹
local notation "𝓎" => yAt M s t c
local notation "𝓍" => xAt M s t c
local notation "𝓊" => rawNodes M s t c
local notation "𝓑" => bStar M s t c
local notation "𝒥" => Jpoly s t
local notation "𝒦" => Geometry.KR (geometry M s t c) 1

include seed in
private theorem invz_ne : γ ≠ 0 := inv_ne_zero (literal_z_pos M s t c seed).ne'

private theorem y_scale (i : Fin 6) : 𝓎 i = γ * 𝓊 i := by
  rw [norm_nodes,div_eq_mul_inv,mul_comm]

include seed in
private theorem j_b_ne : (𝒥).eval 𝓑 ≠ 0 := by
  have hb := literal_b_neg M s t c seed
  have hs := seed.sLower
  have ht := seed.tLower
  simp only [Jpoly,cubic,linearFactor,eval_mul,eval_sub,eval_X,eval_C]
  exact mul_ne_zero (mul_ne_zero (by linarith) (by linarith)) (by linarith)

include hm seed in
private theorem kr_comp : (𝒦).comp (γ • X) = ((𝒥).eval 𝓑)⁻¹ • 𝒥 := by
  let Cb := cubic (𝓎 2) (𝓎 3) (𝓎 0)
  have ev (T : ℝ) : Cb.eval (γ * T) = γ^3 * (𝒥).eval T := by
    have e2 : 𝓎 2 = γ*s := y_scale M s t c 2
    have e3 : 𝓎 3 = γ*t := y_scale M s t c 3
    have e0 : 𝓎 0 = γ*1 := y_scale M s t c 0
    simp only [Cb,cubic,Jpoly,linearFactor,eval_mul,eval_sub,eval_X,eval_C,e2,e3,e0]
    ring
  have e4 : 𝓎 4 = γ * 𝓑 := y_scale M s t c 4
  apply Polynomial.funext
  intro T
  change ((atOne M (𝓎 4) Cb).comp (γ • X)).eval T = _
  simp only [atOne,eval_comp,Polynomial.eval_smul,eval_X,smul_eq_mul,evalAt_eq_eval M hm,e4,ev]
  have hZ := (literal_z_pos M s t c seed).ne'
  field_simp [invz_ne M s t c seed, j_b_ne M s t c seed, hZ] <;> ring

include hm seed in
private theorem shifted_K (T : ℝ) :
    ((𝒢).I 𝒦).eval (γ*T) - γ * (𝒦).eval (γ*T) =
      (γ / (𝒥).eval 𝓑) * (coefficientPrimitive M 𝒥 - 𝒥).eval T := by
  have E := kr_comp M hm s t c seed
  have I := primitive_comp_scale M hm γ 𝒦
  rw [E,map_smul,smul_smul] at I
  have ek := congrArg (fun P : ℙ => P.eval T) E
  have ei := congrArg (fun P : ℙ => P.eval T) I
  change (((𝒦).comp (γ • X)).eval T) = _ at ek
  change (((coefficientPrimitive M 𝒦).comp (γ • X)).eval T) = _ at ei
  simp only [eval_comp,Polynomial.eval_smul,smul_eq_mul,eval_X] at ek ei
  change (coefficientPrimitive M 𝒦).eval (γ*T) - γ*(𝒦).eval (γ*T) = _
  rw [ek,ei,eval_sub,div_eq_mul_inv]
  ring

include hm seed in
private theorem pair_pulled (H : ℙ) (hH : PolyBound 3 H) :
    pairLeft 𝒢 𝒦 H = (γ / (𝒥).eval 𝓑) *
      rawMean M (zAt s) ((H.comp (1 - γ • X)) * (coefficientPrimitive M 𝒥 - 𝒥)) := by
  let D := coefficientPrimitive M 𝒥 - 𝒥
  let P := (H.comp (1 - γ • X)) * D
  have dD : PolyBound 4 D :=
    pSub (primitive_degree M hm 3 𝒥 (pJ s t)) (pUpper (by decide) (pJ s t))
  have dP : PolyBound 7 P := pMul 3 4 _ _ (affineCompBound H γ 3 hH) dD
  have payment := raw_rule_exact7 M hm s t c seed P dP
  have eX (i : Fin 6) : H.eval (𝓍 i) = (H.comp (1 - γ • X)).eval (𝓊 i) := by
    rw [eval_comp,eval_sub,eval_one,Polynomial.eval_smul,eval_X,smul_eq_mul]
    change H.eval (1 - 𝓎 i) = _
    rw [y_scale M s t c i]
  have eY (i : Fin 6) :
      ((𝒢).Ey ((𝒢).I 𝒦)) i - γ * ((𝒢).Ey 𝒦) i = (γ / (𝒥).eval 𝓑) * D.eval (𝓊 i) := by
    change evalAt M (𝓎 i) ((𝒢).I 𝒦) - γ * evalAt M (𝓎 i) 𝒦 = _
    rw [evalAt_eq_eval M hm,evalAt_eq_eval M hm,y_scale M s t c i]
    exact shifted_K M hm s t c seed (𝓊 i)
  change wDot (𝒢).W ((𝒢).Ex H) ((𝒢).Ey ((𝒢).I 𝒦) - γ • (𝒢).Ey 𝒦) = _
  rw [rawMean_apply, ← payment, weightedEval_apply, Finset.mul_sum]
  unfold wDot
  apply Finset.sum_congr rfl
  intro i _
  change (𝒢).W i * evalAt M (𝓍 i) H *
    (((𝒢).Ey ((𝒢).I 𝒦)) i - γ * ((𝒢).Ey 𝒦) i) =
      (γ / (𝒥).eval 𝓑) * ((𝒢).W i * P.eval (𝓊 i))
  rw [evalAt_eq_eval M hm, eX i, eY i]
  dsimp only [P]
  rw [eval_mul]
  ring

private theorem pull_factor (i : Fin 6) :
    (linearFactor (𝓍 i)).comp (1 - γ • X) = (-γ) • linearFactor (𝓊 i) := by
  apply Polynomial.funext
  intro T
  simp only [linearFactor, eval_comp, eval_sub, eval_one, Polynomial.eval_smul, eval_X, eval_C,
    smul_eq_mul, xAt, Pi.sub_apply, Pi.one_apply, y_scale M s t c i]
  ring

include hm seed in
private theorem raw_nodal_avg_zero :
    rawMean M (zAt s) (Bstar M s t * Zpoly s t) = 0 := by
  have hP := pMul 2 4 _ _ (pB M s t c seed.cRoot) (pZ s t)
  have e := raw_rule_exact7 M hm s t c seed _ (pUpper (by decide : 6 ≤ 7) hP)
  rw [← rawMean_apply] at e
  rw [← raw_nodal_factor M s t c seed.cRoot] at e
  have ev (i : Fin 6) : (Lagrange.nodal Finset.univ 𝓊).eval (𝓊 i) = 0 :=
    Lagrange.eval_nodal_at_node (Finset.mem_univ i)
  rw [← raw_nodal_factor M s t c seed.cRoot]
  simpa only [weightedEval_apply,ev,mul_zero,Finset.sum_const_zero] using e.symm

local notation "P₀" => (linearFactor (𝓍 1) * linearFactor (𝓍 5))
local notation "P₁" => ((X : ℙ) * P₀)
local notation "Rᵤ" => cubic (𝓍 1) (𝓍 4) (𝓍 5)
local notation "B₀" => (linearFactor (aAt s) * linearFactor c)
local notation "Ω" => (coefficientPrimitive M 𝒥 - 𝒥)
local notation "Jₛ" => rawMean M (zAt s)

private theorem P₀_degree : PolyBound 2 P₀ :=
  pMul 1 1 _ _ (pFactor _) (pFactor _)

private theorem P₁_degree : PolyBound 3 P₁ :=
  pMul 1 2 _ _ pX (P₀_degree M s t c)

private theorem Ru_degree : PolyBound 3 Rᵤ :=
  pMul 2 1 _ _ (pMul 1 1 _ _ (pFactor _) (pFactor _)) (pFactor _)

private theorem P0_pull : (P₀).comp (1 - γ • X) = γ^2 • B₀ := by
  rw [mul_comp, pull_factor M s t c 1, pull_factor M s t c 5, smul_mul_smul_comm]
  change ((-γ) * (-γ)) • B₀ = _
  rw [neg_mul_neg, pow_two]

private theorem P1_pull : (P₁).comp (1 - γ • X) = γ^2 • (B₀ - γ • (X * B₀)) := by
  rw [mul_comp, X_comp, P0_pull M s t c, mul_smul_comm]
  simp only [sub_mul, one_mul, smul_mul_assoc]

include seed in
private theorem Ru_pull : (Rᵤ).comp (1 - γ • X) = -(γ^3) • (linearFactor (aAt s) * Bstar M s t) := by
  unfold cubic
  rw [mul_comp, mul_comp, pull_factor M s t c 1, pull_factor M s t c 4,
    pull_factor M s t c 5, smul_mul_smul_comm, smul_mul_smul_comm,
    beta_factor M s t c seed.cRoot]
  change ((-γ * -γ) * -γ) • ((linearFactor (aAt s) * linearFactor 𝓑) * linearFactor c) =
    -(γ^3) • (linearFactor (aAt s) * (linearFactor 𝓑 * linearFactor c))
  rw [mul_assoc (linearFactor (aAt s)) (linearFactor 𝓑) (linearFactor c)]
  have e : (-γ * -γ) * -γ = -(γ^3) := by ring
  rw [e]

include hm seed in
private theorem p0_lambda :
    pairLeft 𝒢 𝒦 P₀ = (γ^3 / (𝒥).eval 𝓑) * ellAvg M s t c 0 := by
  rw [pair_pulled M hm s t c seed P₀ (pUpper (by decide) (P₀_degree M s t c)),
    P0_pull M s t c, smul_mul_assoc, map_smul, smul_eq_mul]
  have e : Jₛ (B₀ * Ω) = ellAvg M s t c 0 := by
    rw [rawMean_apply]
    unfold ellAvg
    rw [pow_zero,one_mul] <;> rfl
  rw [e]
  ring

include hm seed in
private theorem p1_lambda :
    pairLeft 𝒢 𝒦 P₁ = (γ^3 / (𝒥).eval 𝓑) * (ellAvg M s t c 0 - γ * ellAvg M s t c 1) := by
  rw [pair_pulled M hm s t c seed P₁ (P₁_degree M s t c), P1_pull M s t c,
    smul_mul_assoc, sub_mul, smul_mul_assoc, map_smul, map_sub, map_smul, smul_eq_mul, smul_eq_mul]
  have e0 : Jₛ (B₀ * Ω) = ellAvg M s t c 0 := by
    rw [rawMean_apply]
    unfold ellAvg
    rw [pow_zero,one_mul] <;> rfl
  have e1 : Jₛ ((X * B₀) * Ω) = ellAvg M s t c 1 := by
    rw [rawMean_apply]
    unfold ellAvg
    rw [pow_one,mul_assoc X (linearFactor (aAt s)) (linearFactor c)] <;> rfl
  rw [e0,e1]
  ring

include hm seed in
private theorem Ru_lambda_ne : pairLeft 𝒢 𝒦 Rᵤ ≠ 0 := by
  rw [pair_pulled M hm s t c seed Rᵤ (Ru_degree M s t c), Ru_pull M s t c seed,
    smul_mul_assoc, map_smul, smul_eq_mul]
  have q : (linearFactor (aAt s) * Bstar M s t) * 𝒥 = Bstar M s t * Zpoly s t := by
    unfold Zpoly
    ring
  have e0 : Jₛ ((linearFactor (aAt s) * Bstar M s t) * Ω) = residualJ0 M s t := by
    change Jₛ ((linearFactor (aAt s) * Bstar M s t) * (coefficientPrimitive M 𝒥 - 𝒥)) = _
    rw [mul_sub,map_sub,q,raw_nodal_avg_zero M hm s t c seed,sub_zero,rawMean_apply] <;> rfl
  rw [e0]
  exact mul_ne_zero (div_ne_zero (invz_ne M s t c seed) (j_b_ne M s t c seed))
    (mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero 3 (invz_ne M s t c seed))) seed.residualPos.ne')

include seed in
private theorem x1_scale : 𝓍 1 = γ * s := by
  change 1 - 𝓎 1 = _
  rw [y_scale M s t c 1]
  change 1 - γ*aAt s = γ*s
  have h : γ * (aAt s + s) = 1 := inv_mul_cancel₀ (literal_z_pos M s t c seed).ne'
  linear_combination -h

include seed in
private theorem x5_scale : 𝓍 5 = γ * (zAt s - c) := by
  change 1 - 𝓎 5 = _
  rw [y_scale M s t c 5]
  change 1 - γ*c = γ*(zAt s-c)
  have h : γ*zAt s=1 := inv_mul_cancel₀ (literal_z_pos M s t c seed).ne'
  linear_combination -h

include seed in
private theorem p0_eval (T : ℝ) :
    (P₀).eval (γ*T) = γ^2 * (T-s) * (T-(zAt s-c)) := by
  simp only [linearFactor, eval_mul, eval_sub, eval_X, eval_C,
    x1_scale M s t c seed, x5_scale M s t c seed]
  ring

include seed in
private theorem p1_eval (T : ℝ) :
    (P₁).eval (γ*T) = γ^3 * T * (T-s) * (T-(zAt s-c)) := by
  rw [eval_mul,eval_X,p0_eval M s t c seed]
  ring

private theorem affine_selector_eq (T : ℝ) :
    affineFor s
      (fun U => (U-(zAt s-c)) *
        ((ellAvg M s t c 0*zAt s-ellAvg M s t c 1) + (-ellAvg M s t c 0)*U)) T =
      affineAt M s t c T := by
  let u := ellAvg M s t c 0*zAt s-ellAvg M s t c 1
  let v := -ellAvg M s t c 0
  have e : (fun U => (U-(zAt s-c))*(u+v*U)) = selectorQuadAt M s t c := by
    funext U
    dsimp only [u,v,selectorQuadAt]
    ring
  change affineFor s (fun U => (U-(zAt s-c))*(u+v*U)) T = _
  rw [e] <;> rfl

include hm seed in
private theorem selector_det :
    let rho := clean M s (dAt M s t c)
    let lam := pairLeft 𝒢 𝒦
    lam P₁ * rho P₀ - lam P₀ * rho P₁ = 0 := by
  let d := dAt M s t c
  let rho := clean M s d
  let lam := pairLeft 𝒢 𝒦
  let P := lam P₁ • P₀ - lam P₀ • P₁
  let m := zAt s-c
  let u := ellAvg M s t c 0*zAt s-ellAvg M s t c 1
  let v := -ellAvg M s t c 0
  let j := fun T => (T-m)*(u+v*T)
  let k := γ^6 / (𝒥).eval 𝓑
  have hγz : γ*(zAt s)=1 := inv_mul_cancel₀ (literal_z_pos M s t c seed).ne'
  have evP (T : ℝ) : P.eval (γ*T) = k * ((T-s)*j T) := by
    simp only [P,eval_sub,Polynomial.eval_smul,smul_eq_mul,p0_eval M s t c seed,
      p1_eval M s t c seed,lam,p0_lambda M hm s t c seed,p1_lambda M hm s t c seed,k,j,m,u,v]
    simp only [div_eq_mul_inv]
    linear_combination -(γ^5 * ((𝒥).eval 𝓑)⁻¹ * (T-s)*(T-(zAt s-c))*ellAvg M s t c 0) * hγz
  have hlo := seed.sLower
  have hhi := seed.sUpper
  have root : seedCubic s = 0 := seed.sRoot
  obtain ⟨hdlo,_,hdroot⟩ := calibrated_real_bracket M s t c seed.affineLowerNeg seed.affineUpperPos
  have hL := Ld_pos s d hlo hhi root hdlo
  have e := response_factor s d m u v (by linarith) (by linarith) root hL.ne'
  change Ld s (etaAt s) d * response s d (fun T => (T-s)*j T) =
    (d-s)*(d-1)*(d-aAt s)*affineFor s j d at e
  have ej : affineFor s j d = affineAt M s t c d := affine_selector_eq M s t c d
  rw [ej,hdroot,mul_zero] at e
  have rr := (mul_eq_zero.mp e).resolve_left hL.ne'
  have rp : rho P = 0 := by
    change clean M s d P = 0
    rw [clean_response M hm,show (fun T => P.eval (γ*T)) = (fun T => k*((T-s)*j T)) by
      funext T; exact evP T, response_scale,rr,mul_zero]
  change rho (lam P₁ • P₀ - lam P₀ • P₁) = 0 at rp
  simpa only [map_sub,map_smul,smul_eq_mul] using rp

include hm seed in
private theorem probe_nonzero :
    clean M s (dAt M s t c) (P₁ - (γ*rAt s) • P₀) ≠ 0 := by
  let d := dAt M s t c
  let m := zAt s-c
  let Q := P₁ - (γ*rAt s) • P₀
  have eQ (T : ℝ) : Q.eval (γ*T) =
      γ^3 * ((T-s)*((T-m)*(-rAt s+1*T))) := by
    simp only [Q,eval_sub,Polynomial.eval_smul,smul_eq_mul,p0_eval M s t c seed,
      p1_eval M s t c seed,m]
    ring
  have hlo := seed.sLower
  have hhi := seed.sUpper
  have root : seedCubic s = 0 := seed.sRoot
  obtain ⟨hdlo,_,_⟩ := calibrated_real_bracket M s t c seed.affineLowerNeg seed.affineUpperPos
  have hL := Ld_pos s d hlo hhi root hdlo
  have ei := response_plane_nonzero s d m (by linarith) (by linarith) root
    hL.ne' (by linarith) (sub_neg.mpr seed.cRight)
  change clean M s d Q ≠ 0
  rw [clean_response M hm,show (fun T => Q.eval (γ*T)) =
      (fun T => γ^3*((T-s)*((T-m)*(-rAt s+1*T)))) by funext T; exact eQ T,
    response_scale]
  exact mul_ne_zero (pow_ne_zero 3 (invz_ne M s t c seed)) ei

include hm seed in
/-- The last missing paid moment for the actual H4,K4. Apart from the
standard basis, its inputs are explicit fields of ExactScalarSeed. -/
theorem literal_calibration_cell :
    (𝒢).pairing ((𝒢).HF 0) ((𝒢).KR 1) = 0 := by
  let rho := clean M s (dAt M s t c)
  let lam := pairLeft 𝒢 𝒦
  let e := (evalAt M (𝓍 4) P₀)⁻¹
  have er : Rᵤ = P₁ - (𝓍 4) • P₀ := by
    simp only [cubic,linearFactor,smul_eq_C_mul]
    ring
  have eh : (𝒢).HF 0 = e • P₀ - (rho (e • P₀) / rho Rᵤ) • Rᵤ := rfl
  exact elimination rho lam P₀ P₁ Rᵤ ((𝒢).HF 0) (𝓍 4) (γ*rAt s) e
    er eh (Ru_lambda_ne M hm s t c seed) (probe_nonzero M hm s t c seed)
    (selector_det M hm s t c seed)

include hm seed in
/-- All seven scalar leaves of the pending literal Fin11 producer.
There is no additional executable sign check, rank hypothesis, or cell. -/
theorem literal_scalar_leaves : ConditionalFin11.ScalarLeaves 𝒢 := by
  have q := quadrature_green_of_exact_seed M hm s t c seed
  exact ⟨literal_mass_nonzero M hm s t c seed, q.quadrature, q.clock,
    q.primitiveBound,q.clockBound,q.green,literal_calibration_cell M hm s t c seed⟩

include hm seed in
theorem literal_residual_pivot :
    ForwardCubics.ResidualPivot M s t c := by
  let rho := clean M s (dAt M s t c)
  let lam := pairLeft 𝒢 𝒦
  have eR : Rᵤ = P₁ - (𝓍 4) • P₀ := by
    simp only [cubic,linearFactor,smul_eq_C_mul]
    ring
  have det := selector_det M hm s t c seed
  change lam P₁ * rho P₀ - lam P₀ * rho P₁ = 0 at det
  have lR : lam Rᵤ = lam P₁ - (𝓍 4) * lam P₀ := by
    rw [eR,map_sub,map_smul,smul_eq_mul]
  change rho Rᵤ ≠ 0
  intro zr
  rw [eR,map_sub,map_smul,smul_eq_mul] at zr
  have e1 := sub_eq_zero.mp zr
  rw [e1] at det
  have aux : lam Rᵤ * rho P₀ = 0 := by
    rw [lR]
    linear_combination det
  have z0 := (mul_eq_zero.mp aux).resolve_left (Ru_lambda_ne M hm s t c seed)
  have z1 : rho P₁ = 0 := by rw [e1,z0,mul_zero]
  apply probe_nonzero M hm s t c seed
  change rho (P₁ - (γ*rAt s) • P₀) = 0
  rw [map_sub,map_smul,smul_eq_mul,z0,z1,mul_zero,sub_self]

end Literal

end RKResearch.Certified.PaidDefectBridge.SDIRK118.ScalarCalibration
