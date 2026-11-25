module

public import RKCert.ReviewedNative.SDIRK118ScalarAffineResponse
public import Mathlib.Algebra.Polynomial.Basis
public import RKCert.ReviewedNative.RealCubicOrderBracket

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

noncomputable section

namespace RKResearch.Certified.PaidDefectBridge.SDIRK118.ScalarExistence

open ClaimPin ScalarBindings ScalarQuadrature
open ScalarAffineResponse (seedCubic eta_clear iota)
open Polynomial
open scoped BigOperators Polynomial

def sLo : ℝ := 457148959716 / (2:ℝ)^40
def sHi : ℝ := 457148959717 / (2:ℝ)^40
def tLo : ℝ := 138977439915 / (2:ℝ)^40
def tHi : ℝ := 138977439916 / (2:ℝ)^40
def cLo : ℝ := 1270550 / (2:ℝ)^20
def cHi : ℝ := 1270551 / (2:ℝ)^20

private theorem cubic_seed (x : ℝ) :
    RKCert.ReviewedNative.RealCubicOrderBracket.cubic 1 (-9) 18 (-6) x =
      seedCubic x := by
  unfold RKCert.ReviewedNative.RealCubicOrderBracket.cubic seedCubic
  ring

private theorem cubic_qSeed (s x : ℝ) :
    RKCert.ReviewedNative.RealCubicOrderBracket.cubic 0 1 (-(s+3)) s x =
      qSeed s x := by
  unfold RKCert.ReviewedNative.RealCubicOrderBracket.cubic qSeed
  ring

private theorem cubic_quadratic (M : MonomialBasis) (s t x : ℝ) :
    RKCert.ReviewedNative.RealCubicOrderBracket.cubic
        0 1 (beta1 M s t) (beta0 M s t) x =
      quadraticAt M s t x := by
  simp only [RKCert.ReviewedNative.RealCubicOrderBracket.cubic,quadraticAt,
    zero_mul,zero_add,one_mul]

private theorem qSeed_le (T : ℝ) (hT : T ≤ 1) {s s' : ℝ} (hs : s ≤ s') :
    qSeed s T ≤ qSeed s' T := by
  apply sub_nonneg.mp
  rw [show qSeed s' T - qSeed s T = (s' - s)*(1-T) by unfold qSeed; ring]
  exact mul_nonneg (sub_nonneg.mpr hs) (sub_nonneg.mpr hT)

/-- The cubic and the decreasing quadratic use only the fixed rational
brackets. No uniform moment or affine signs are needed for these roots. -/
theorem exists_seed_pair :
    ∃ s ∈ Set.Ioo sLo sHi, ∃ t ∈ Set.Ioo tLo tHi,
      seedCubic s = 0 ∧ qSeed s t = 0 := by
  have sneg : seedCubic sLo < 0 := by norm_num [seedCubic,sLo]
  have spos : 0 < seedCubic sHi := by norm_num [seedCubic,sHi]
  obtain ⟨s,hs,hs0⟩ :=
    RKCert.ReviewedNative.RealCubicOrderBracket.exists_strict_root
      1 (-9) 18 (-6) (l:=sLo) (r:=sHi)
      (by norm_num [sLo]) (by norm_num [sLo,sHi]) (by norm_num [sHi])
      (Or.inl (by simpa only [cubic_seed] using And.intro sneg spos))
  have lo0 : 0 < qSeed sLo tLo := by norm_num [qSeed,sLo,tLo]
  have hi0 : qSeed sHi tHi < 0 := by norm_num [qSeed,sHi,tHi]
  have lo : 0 < qSeed s tLo :=
    lo0.trans_le (qSeed_le tLo (by norm_num [tLo]) hs.1.le)
  have hi : qSeed s tHi < 0 :=
    (qSeed_le tHi (by norm_num [tHi]) hs.2.le).trans_lt hi0
  obtain ⟨t,ht,ht0⟩ :=
    RKCert.ReviewedNative.RealCubicOrderBracket.exists_strict_root
      0 1 (-(s+3)) s (l:=tLo) (r:=tHi)
      (by norm_num [tLo]) (by norm_num [tLo,tHi]) (by norm_num [tHi])
      (Or.inr (by simpa only [cubic_qSeed] using And.intro lo hi))
  exact ⟨s,hs,t,ht,by simpa only [cubic_seed] using hs0,
    by simpa only [cubic_qSeed] using ht0⟩

/-- The exact rational moment evaluator used by the scalar sign receipts. -/
theorem avg_pow_for_certificate (M : MonomialBasis) (hM : standardPowers M)
    (z : ℝ) (hz : z ≠ 0) (n : ℕ) :
    avg M z ((X : Polynomial ℝ)^n) = z^n / ((n+1:ℕ):ℝ) := by
  rw [← mean_scale M hM z hz, X_pow_comp, smul_pow, map_smul, mean_pow M hM,
    smul_eq_mul, div_eq_mul_inv]

private theorem avg_smul_for_certificate (M : MonomialBasis) (z a : ℝ)
    (P : Polynomial ℝ) : avg M z (a • P) = a * avg M z P := by
  unfold avg
  rw [map_smul,map_smul,smul_eq_mul,mul_div_assoc]

theorem avg_eq_coefficient_sum (M : MonomialBasis) (hM : standardPowers M)
    (z : ℝ) (hz : z ≠ 0) (P : Polynomial ℝ) (n : ℕ) (hp : P.natDegree < n) :
    avg M z P =
      ∑ k ∈ Finset.range n, P.coeff k * (z^k / ((k+1:ℕ):ℝ)) := by
  have hP : P = ∑ k ∈ Finset.range n, P.coeff k • (X : Polynomial ℝ)^k := by
    simpa only [smul_eq_C_mul,C_mul_X_pow_eq_monomial] using P.as_sum_range' n hp
  calc
    avg M z P = ∑ k ∈ Finset.range n, avg M z (P.coeff k • (X : Polynomial ℝ)^k) := by
      unfold avg
      conv_lhs => rw [hP]
      rw [map_sum,map_sum,Finset.sum_div]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      rw [avg_smul_for_certificate, avg_pow_for_certificate M hM z hz]

theorem primitive_coeff_zero_for_certificate (M : MonomialBasis)
    (hM : standardPowers M) (P : Polynomial ℝ) :
    (coefficientPrimitive M P).coeff 0 = 0 := by
  rw [coeff_zero_eq_eval_zero]
  exact primitive_eval_zero M hM P

theorem primitive_coeff_succ_for_certificate (M : MonomialBasis)
    (hM : standardPowers M) (P : Polynomial ℝ) (n : ℕ) :
    (coefficientPrimitive M P).coeff (n+1) = P.coeff n / ((n+1:ℕ):ℝ) := by
  have h := congrArg (fun Q : Polynomial ℝ => Q.coeff n) (derivative_primitive M hM P)
  change (derivative (coefficientPrimitive M P)).coeff n = P.coeff n at h
  rw [coeff_derivative] at h
  exact (eq_div_iff (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n))).2 (by simpa only [Nat.cast_add, Nat.cast_one] using h)

/-- The denominator-cleared quadratic in the fixed endpoint receipt. -/
def clearedQuad (M : MonomialBasis) (s t c : ℝ) : ℝ :=
  momentDet M s t*c^2+
    (μ M s t 1*μ M s t 2-μ M s t 0*μ M s t 3)*c+
    (μ M s t 1*μ M s t 3-(μ M s t 2)^2)

theorem clearedQuad_eq (M : MonomialBasis) (s t c : ℝ)
    (hD : momentDet M s t ≠ 0) :
    clearedQuad M s t c = momentDet M s t * quadraticAt M s t c := by
  unfold clearedQuad quadraticAt beta1 beta0
  field_simp [hD] <;> ring

def etaBox (s : ℝ) : ℝ := (3+s)/(4*(3-s))

/-- This is the unscaled response in the sign receipt, with the
rational eta formula. It is not the normalized signed selector. -/
def affineBoxValue (M : MonomialBasis) (s t c T : ℝ) : ℝ :=
  let η := etaBox s
  let a := aAt s
  let r := s/3
  let j := selectorQuadAt M s t c
  Ld s η T * j r / ((1-r)*(a-r)) -
    ((η*Bs s-3*(Bs s-1-η))/3) * iota r a j T

theorem affineAt_eq_boxValue (M : MonomialBasis) (s t c T : ℝ)
    (hs : seedCubic s = 0) (h3 : 3-s ≠ 0) :
    affineAt M s t c T = affineBoxValue M s t c T := by
  have he : etaAt s = etaBox s := by
    unfold etaBox
    apply (eq_div_iff (mul_ne_zero (by norm_num : (4:ℝ) ≠ 0) h3)).2
    exact (mul_comm _ _).trans (eta_clear s hs)
  simp only [affineAt, affineBoxValue, iota, he]

/-- Exactly the three as-yet-unbound groups of fixed-box signs. This does
not assume a root, a value of the calibration coordinate, or any donor. -/
structure BoxSignBindings (M : MonomialBasis) : Prop where
  quadratic : ∀ s ∈ Set.Icc sLo sHi, ∀ t ∈ Set.Icc tLo tHi,
    0 < momentDet M s t ∧ clearedQuad M s t 0 < 0 ∧
      clearedQuad M s t cLo < 0 ∧ 0 < clearedQuad M s t cHi
  oldGuards : ∀ s ∈ Set.Icc sLo sHi, ∀ t ∈ Set.Icc tLo tHi,
    (∀ i : Fin 4, omegaOld M s t i ≠ 0) ∧ 0 < residualJ0 M s t
  affine : ∀ s ∈ Set.Icc sLo sHi, ∀ t ∈ Set.Icc tLo tHi,
    ∀ c ∈ Set.Icc cLo cHi,
      affineBoxValue M s t c (15/4) < 0 ∧ 0 < affineBoxValue M s t c 4

theorem exact_seed_of_box_signs (M : MonomialBasis) (signs : BoxSignBindings M) :
    ∃ (s t c : ℝ), ExactScalarSeed M s t c := by
  obtain ⟨s,hs,t,ht,hs0,ht0⟩ := exists_seed_pair
  have hs' : s ∈ Set.Icc sLo sHi := ⟨hs.1.le,hs.2.le⟩
  have ht' : t ∈ Set.Icc tLo tHi := ⟨ht.1.le,ht.2.le⟩
  obtain ⟨hD,hQ0,hQl,hQr⟩ := signs.quadratic s hs' t ht'
  have qneg (x : ℝ) (hx : clearedQuad M s t x < 0) :
      quadraticAt M s t x < 0 := by
    apply lt_of_mul_lt_mul_left (a:=momentDet M s t) _ hD.le
    rw [mul_zero, ← clearedQuad_eq M s t x hD.ne']
    exact hx
  have qpos : 0 < quadraticAt M s t cHi := by
    apply lt_of_mul_lt_mul_left (a:=momentDet M s t) _ hD.le
    rw [mul_zero, ← clearedQuad_eq M s t cHi hD.ne']
    exact hQr
  obtain ⟨c,hc,hc0⟩ :=
    RKCert.ReviewedNative.RealCubicOrderBracket.exists_strict_root
      0 1 (beta1 M s t) (beta0 M s t) (l:=cLo) (r:=cHi)
      (by norm_num [cLo]) (by norm_num [cLo,cHi]) (by norm_num [cHi])
      (Or.inl (by simpa only [cubic_quadratic] using And.intro (qneg cLo hQl) qpos))
  have hc' : c ∈ Set.Icc cLo cHi := ⟨hc.1.le,hc.2.le⟩
  obtain ⟨ho,hj⟩ := signs.oldGuards s hs' t ht'
  obtain ⟨ha,hb⟩ := signs.affine s hs' t ht' c hc'
  have zs : zAt s < cLo := by
    calc
      zAt s ≤ zAt sHi := by unfold zAt aAt; linarith only [hs'.2]
      _ < cLo := by norm_num [zAt,aAt,sHi,cLo]
  have h3 : 3-s ≠ 0 := by
    have h : s < (3:ℝ) := hs.2.trans (by norm_num [sHi])
    exact (sub_pos.mpr h).ne'
  refine ⟨s,t,c, {
    sLower := (show (13/32:ℝ) < sLo by norm_num [sLo]).trans hs.1
    sUpper := hs.2.trans (by norm_num [sHi])
    sRoot := hs0
    tLower := (show (1/8:ℝ) < tLo by norm_num [tLo]).trans ht.1
    tUpper := ht.2.trans (by norm_num [tHi])
    tRoot := ht0
    momentPivotPos := hD
    quadAtZeroNeg := qneg 0 hQ0
    cRight := zs.trans hc.1
    cRoot := by simpa only [cubic_quadratic] using hc0
    omegaNe := ho
    residualPos := hj
    affineLowerNeg := ?_
    affineUpperPos := ?_ }⟩
  · rw [affineAt_eq_boxValue M s t c _ hs0 h3]
    exact ha
  · rw [affineAt_eq_boxValue M s t c _ hs0 h3]
    exact hb

/-- The universal basis in the sealed target adds no guard: standard
powers determine the actual basis. Only one set of sign receipts is needed. -/
theorem scalarExistenceTarget_of_box_signs
    (signs : BoxSignBindings (Polynomial.basisMonomials ℝ)) : ScalarExistenceTarget := by
  intro M hM
  have e : M = Polynomial.basisMonomials ℝ := DFunLike.ext _ _ (by
    intro n
    change M n = Polynomial.monomial n (1:ℝ)
    rw [hM n, Polynomial.monomial_one_right_eq_X_pow])
  rw [e]
  exact exact_seed_of_box_signs _ signs

end RKResearch.Certified.PaidDefectBridge.SDIRK118.ScalarExistence
