module

public import RKCert.ReviewedNative.SDIRK118ScalarMasses

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

noncomputable section

namespace RKResearch.Certified.PaidDefectBridge.SDIRK118.ScalarAffineResponse

open RKResearch.Certified.PaidDefectBridge.ForwardChart (tiltA tiltB)
open RKResearch.Certified.PaidDefectBridge.SDIRK118.ScalarBindings

def seedCubic (s : ℝ) : ℝ := s ^ 3 - 9 * s ^ 2 + 18 * s - 6
def rAt (s : ℝ) : ℝ := s / 3
def leadAt (s : ℝ) : ℝ := etaAt s * Bs s - 3 * (Bs s - 1 - etaAt s)

/-- The shared scalar evaluated affine interpolant, not a polynomial
rank declaration. Only its values at the frozen finite nodes are used. -/
def iota (r a : ℝ) (j : ℝ → ℝ) (T : ℝ) : ℝ :=
  ((T - a) * j 1 / (1 - r) - (T - 1) * j a / (a - r)) / (1 - a)

def affineFor (s : ℝ) (j : ℝ → ℝ) (T : ℝ) : ℝ :=
  Ld s (etaAt s) T * j (rAt s) / ((1 - rAt s) * (aAt s - rAt s)) -
    (leadAt s / 3) * iota (rAt s) (aAt s) j T

def response (s d : ℝ) (f : ℝ → ℝ) : ℝ :=
  let a := aAt s
  let gd := gdAt s (etaAt s) d
  f d + tiltA a d (1/2) gd * f 1 + tiltB a d (g1At s) gd * f a

theorem eta_clear (s : ℝ) (hs : seedCubic s = 0) :
    (4 * (3 - s)) * etaAt s = 3 + s := by
  unfold seedCubic at hs
  unfold etaAt g1At hAt aAt
  linear_combination hs

private theorem eta_ratio (s : ℝ) (hs3 : 3 - s ≠ 0) (hs : seedCubic s = 0) :
    etaAt s = (3 + s) / (4 * (3 - s)) := by
  apply (eq_div_iff (mul_ne_zero (by norm_num) hs3)).2
  rw [mul_comm]
  exact eta_clear s hs

/-- The exact quadratic factor identity; no evaluation at a candidate root. -/
theorem seed_factor (s T : ℝ) (hs3 : 3 - s ≠ 0) (hs : seedCubic s = 0) :
    etaAt s * Bs s * qSeed s T - (3 * T - s) * Ld s (etaAt s) T =
      leadAt s * (T - 1) * (T - aAt s) := by
  let D := fun U => etaAt s * Bs s * qSeed s U - (3 * U - s) * Ld s (etaAt s) U -
    leadAt s * (U - 1) * (U - aAt s)
  have d1 : D 1 = 0 := by dsimp [D, Ld, qSeed, Bs]; ring
  have d0Scale : (8 * (3 - s)) * D 0 = -3 * (3 + s) * seedCubic s := by
    dsimp only [D]
    unfold leadAt Ld qSeed Bs aAt seedCubic
    rw [eta_ratio s hs3 hs]
    field_simp [hs3] <;> ring
  have d0 : D 0 = 0 := by
    rw [hs, mul_zero] at d0Scale
    exact (mul_eq_zero.mp d0Scale).resolve_left (mul_ne_zero (by norm_num) hs3)
  have aff : D T = T * D 1 + (1 - T) * D 0 := by
    dsimp [D,leadAt,Ld,qSeed]
    ring
  simp only [d0,d1,mul_zero,add_zero] at aff
  exact sub_eq_zero.mp aff

theorem lead_ne (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (hs : seedCubic s = 0) :
    leadAt s ≠ 0 := by
  have hs3 : 0 < 3 - s := by linarith
  have hB : 0 < Bs s := mul_pos (sub_pos.mpr hs1) hs3
  have heta : 0 < etaAt s := by
    rw [eta_ratio s hs3.ne' hs]
    exact div_pos (by linarith) (mul_pos (by norm_num) hs3)
  have hq : qSeed s (rAt s) ≠ 0 := by
    have v : qSeed s (rAt s) = -(2 * s ^ 2 / 9) := by unfold qSeed rAt; ring
    rw [v]
    exact neg_ne_zero.mpr (div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hs0.ne')) (by norm_num))
  intro h0
  have eq := seed_factor s (rAt s) hs3.ne' hs
  have er : 3 * rAt s - s = 0 := by unfold rAt; ring
  simp only [h0, er, zero_mul, sub_zero] at eq
  exact (mul_ne_zero (mul_ne_zero heta.ne' hB.ne') hq) eq

/-- A coarse exact lower bound suffices: no evaluation/refinement of d. -/
theorem Ld_pos (s d : ℝ) (hslo : (13/32 : ℝ) < s) (hshi : s < 14/32)
    (hs : seedCubic s = 0) (hd : (15/4 : ℝ) < d) :
    0 < Ld s (etaAt s) d := by
  have hs3 : 0 < 3 - s := by linarith
  have eB : (4 * (3 - s)) * (Bs s - 1) = 8 * s * (2 - s) := by
    unfold seedCubic at hs
    unfold Bs
    linear_combination -4 * hs
  have eL : (4 * (3 - s)) * Ld s (etaAt s) d =
      (8 * s * (2 - s)) * (d - 1) - (3 + s) * (d + 1 - 2 * s) := by
    unfold Ld
    linear_combination (d - 1) * eB - (d + 1 - 2 * s) * (eta_clear s hs)
  have b0 : (663/128 : ℝ) ≤ 8 * s * (2 - s) := by
    have h := mul_nonneg (show 0 ≤ s - 13/32 by linarith)
      (show 0 ≤ 2 - s - 13/32 by linarith)
    nlinarith only [h]
  have b1 : (663/128 : ℝ) * (d - 1) ≤ (8 * s * (2 - s)) * (d - 1) :=
    mul_le_mul_of_nonneg_right b0 (by linarith)
  have b2 : (3 + s) * (d + 1 - 2 * s) ≤ (55/16 : ℝ) * (d + 3/16) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by norm_num)
  have epos : 0 < (4 * (3 - s)) * Ld s (etaAt s) d := by
    rw [eL]
    linarith only [b1,b2,hd]
  exact pos_of_mul_pos_right epos (mul_nonneg (by norm_num) hs3.le)

private theorem interpolation_formula (r a m u v T : ℝ)
    (hr1 : 1 - r ≠ 0) (hra : a - r ≠ 0) (ha1 : 1 - a ≠ 0) :
    let j := fun S : ℝ => (S - m) * (u + v * S)
    j T - (T - r) * iota r a j T =
      j r * (T - 1) * (T - a) / ((1 - r) * (a - r)) := by
  dsimp [iota]
  field_simp [hr1,hra,ha1] <;> ring

/-- The denominator-clear response formula on the entire two-dimensional
plane j(T)=(T-m)(u+vT). This proves its exact affine coefficients. -/
theorem response_factor (s d m u v : ℝ) (hs0 : 0 < s) (hs1 : s < 1)
    (hs : seedCubic s = 0) (hL : Ld s (etaAt s) d ≠ 0) :
    let j := fun T : ℝ => (T - m) * (u + v * T)
    Ld s (etaAt s) d * response s d (fun T => (T - s) * j T) =
      (d - s) * (d - 1) * (d - aAt s) * affineFor s j d := by
  let a := aAt s
  let r := rAt s
  let κ := 3 / (2 * Bs s)
  let η := etaAt s
  let L := Ld s η d
  let gd := gdAt s η d
  let j := fun T : ℝ => (T - m) * (u + v * T)
  let i := iota r a j d
  have hs3 : 3 - s ≠ 0 := by linarith
  have hB : Bs s ≠ 0 := mul_ne_zero (by linarith) hs3
  have hκ : κ ≠ 0 := div_ne_zero (by norm_num) (mul_ne_zero (by norm_num) hB)
  have hr1 : 1 - r ≠ 0 := by dsimp [r,rAt]; linarith
  have hra : a - r ≠ 0 := by dsimp [a,aAt,r,rAt]; linarith
  have ha1 : 1 - a ≠ 0 := by dsimp [a,aAt]; linarith
  have h1a : a - 1 ≠ 0 := by dsimp [a,aAt]; linarith
  have hs' : s ^ 3 - 9 * s ^ 2 + 18 * s - 6 = 0 := hs
  obtain ⟨g0,g1,_⟩ := RKResearch.Certified.PaidDefectBridge.ReverseChart.seedQuad_old_values
    (K := ℝ) s (by linarith) hs3 hs'
  rw [RKResearch.Certified.PaidDefectBridge.ReverseChart.eval_seedQuad] at g0 g1
  change κ * (1 - s) * (1 - r) = (1/2 : ℝ) at g0
  change κ * (a - s) * (a - r) = g1At s at g1
  have haS : a - s ≠ 0 := by dsimp [a,aAt]; linarith
  have hs1ne : 1 - s ≠ 0 := by linarith
  have hresponse : response s d (fun T => (T - s) * j T) = (d - s) * j d - gd / κ * i := by
    change (d - s) * j d + tiltA a d (1/2) gd * ((1 - s) * j 1) +
      tiltB a d (g1At s) gd * ((a - s) * j a) = _
    rw [← g0, ← g1]
    dsimp only [tiltA, tiltB, i, iota]
    field_simp [h1a,ha1,hκ,hs1ne,haS,hr1,hra] <;> ring
  have hgd : L * gd = (η / 2) * (d - s) * qSeed s d := by
    change L * (((η / 2) * (d - s) * qSeed s d) / L) = _
    rw [mul_comm L, div_mul_cancel₀ _ hL]
  have hk : (η / 2) / κ = η * Bs s / 3 := by
    dsimp [κ]
    field_simp [hB] <;> ring
  have qi : L * (d - r) - (η * Bs s / 3) * qSeed s d =
      -(leadAt s / 3) * (d - 1) * (d - a) := by
    have e := seed_factor s d hs3 hs
    dsimp only [L,r,rAt,η,a]
    linear_combination -(1/3 : ℝ) * e
  have eqj : j d = (d - r) * i + j r * (d - 1) * (d - a) / ((1 - r) * (a - r)) := by
    have e := interpolation_formula r a m u v d hr1 hra ha1
    change j d - (d - r) * i = _ at e
    linear_combination e
  change L * response s d (fun T => (T - s) * j T) =
    (d - s) * (d - 1) * (d - a) * affineFor s j d
  rw [hresponse]
  calc
    L * ((d - s) * j d - gd / κ * i) =
        (d - s) * (L * j d - ((η / 2) / κ) * qSeed s d * i) := by
      calc
        _ = (d - s) * (L * j d) - (L * gd) / κ * i := by ring
        _ = _ := by rw [hgd]; ring
    _ = _ := by
      rw [hk,eqj]
      calc
        _ = (d - s) * ((L * (d - r) - (η * Bs s / 3) * qSeed s d) * i +
            L * (j r * (d - 1) * (d - a) / ((1 - r) * (a - r)))) := by ring
        _ = _ := by rw [qi]; dsimp only [affineFor]; ring

/-- Single explicit nonzero response on the calibration plane.
No hypothesis of rank, surjectivity, or a selected basis remains. -/
theorem response_plane_nonzero (s d m : ℝ)
    (hs0 : 0 < s) (hs1 : s < 1) (hs : seedCubic s = 0)
    (hL : Ld s (etaAt s) d ≠ 0) (hd : 1 < d) (hm : m < 0) :
    response s d (fun T => (T - s) * ((T - m) * (-rAt s + 1*T))) ≠ 0 := by
  let a := aAt s
  let r := rAt s
  let j := fun T : ℝ => (T - m) * (-r + 1*T)
  have hr1 : 1 - r ≠ 0 := by dsimp [r,rAt]; linarith
  have hra : a - r ≠ 0 := by dsimp [a,aAt,r,rAt]; linarith
  have ha1 : 1 - a ≠ 0 := by dsimp [a,aAt]; linarith
  have eI : iota r a j d = d - m := by
    dsimp [iota,j]
    field_simp [hr1,hra,ha1] <;> ring
  have er : j r = 0 := by dsimp [j]; ring
  have eA : affineFor s j d = -(leadAt s / 3) * (d - m) := by
    change Ld s (etaAt s) d * j r / ((1-r)*(a-r)) -
      (leadAt s/3)*iota r a j d = _
    rw [er,eI,mul_zero,zero_div,zero_sub] <;> ring
  have e := response_factor s d m (-r) 1 hs0 hs1 hs hL
  change Ld s (etaAt s) d * response s d (fun T => (T-s)*j T) =
    (d-s)*(d-1)*(d-a)*affineFor s j d at e
  rw [eA] at e
  have hA : -(leadAt s / 3) * (d - m) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr (div_ne_zero (lead_ne s hs0 hs1 hs) (by norm_num))) (by linarith)
  have hda : d - a ≠ 0 := by dsimp [a,aAt]; linarith
  have hn : (d-s)*(d-1)*(d-a)* (-(leadAt s / 3) * (d - m)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (by linarith) (by linarith)) hda) hA
  intro hz
  change response s d (fun T => (T - s) * j T) = 0 at hz
  rw [hz,mul_zero] at e
  exact hn e.symm

end RKResearch.Certified.PaidDefectBridge.SDIRK118.ScalarAffineResponse
