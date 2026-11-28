module

public import RKCert.ReviewedNative.ERK10FixedQ29AdicScalars
public import Mathlib.Tactic.Ring

@[expose] public section

namespace RKResearch.Certified.ERK10FixedQ29Adic
open Polynomial
open scoped Ring

set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

private theorem inv2 : (2:F)⁻¹ = 15 := by
  apply inv_eq_of_mul_eq_one_right
  decide +kernel

private theorem inv3 : (3:F)⁻¹ = 10 := by
  apply inv_eq_of_mul_eq_one_right
  decide +kernel

private theorem inv5 : (5:F)⁻¹ = 6 := by
  apply inv_eq_of_mul_eq_one_right
  decide +kernel

private theorem inv27 : (27:F)⁻¹ = 14 := by
  apply inv_eq_of_mul_eq_one_right
  decide +kernel

private theorem inv24 : (24:F)⁻¹ = 23 := by
  apply inv_eq_of_mul_eq_one_right
  decide +kernel

private theorem inv4 : (4:F)⁻¹ = 22 := by
  apply inv_eq_of_mul_eq_one_right
  decide +kernel

private theorem inv14 : (14:F)⁻¹ = 27 := by
  apply inv_eq_of_mul_eq_one_right
  decide +kernel

theorem hDen_residue : hDen (2 : F) = 27 := by
  simp only [hDen, wEarly, jm, avg, Ring.inverse_eq_inv, avgDen_two, inv2, inv3, inv5, inv27, inv24, inv4, inv14]
  decide +kernel

theorem hTail_residue : hTail (2 : F) = 22 := by
  simp only [hTail, wEarly, jm, avg, hDen_residue, Ring.inverse_eq_inv, avgDen_two, inv2, inv3, inv5, inv27, inv24, inv4, inv14]
  decide +kernel

theorem fDen_residue : fDen (2 : F) = 27 := by
  simp only [fDen, sFour, m, hTail_residue, avg, Ring.inverse_eq_inv, avgDen_two, inv2, inv3, inv5, inv27, inv24, inv4, inv14]
  decide +kernel

theorem fTail_residue : fTail (2 : F) = 7 := by
  simp only [fTail, sFour, m, hTail_residue, fDen_residue, avg, Ring.inverse_eq_inv, avgDen_two, inv2, inv3, inv5, inv27, inv24, inv4, inv14]
  decide +kernel

theorem eDen_residue : eDen (2 : F) = 24 := by
  simp only [eDen, omegaPoly]
  decide +kernel

theorem eTail_residue : eTail (2 : F) = 27 := by
  simp only [eTail, eDen_residue, Ring.inverse_eq_inv, avgDen_two, inv2, inv3, inv5, inv27, inv24, inv4, inv14]
  decide +kernel

theorem tThree_zero_residue : tThree (2 : F) 0 = 4 := by
  simp only [tThree, fTail_residue, hTail_residue]
  decide +kernel

theorem kMom_residue : kMom (2 : F) = 16 := by
  simp only [kMom, tThree, fTail_residue, hTail_residue, avg, Ring.inverse_eq_inv, avgDen_two, inv2, inv3, inv5, inv27, inv24, inv4, inv14]
  decide +kernel

theorem jMom_residue : jMom (2 : F) = 0 := by
  simp only [jMom, sFour, fTail_residue, hTail_residue, omegaPoly, avg, Ring.inverse_eq_inv, avgDen_two, inv2, inv3, inv5, inv27, inv24, inv4, inv14]
  decide +kernel

theorem origin_residue : origin (2 : F) = 0 := by
  simp only [origin, lMom, kMom_residue, jMom_residue, Ring.inverse_eq_inv, avgDen_two, inv2, inv3, inv5, inv27, inv24, inv4, inv14]
  decide +kernel

theorem qC_residue : qC (2 : F) = 9 := by
  simp only [qC, eTail_residue, kMom_residue]
  decide +kernel

theorem qL_residue : qL (2 : F) = 20 := by
  simp only [qL, lMom, eTail_residue, kMom_residue, jMom_residue, Ring.inverse_eq_inv, avgDen_two, inv2, inv3, inv5, inv27, inv24, inv4, inv14]
  decide +kernel

theorem eZero_residue : eZero (2 : F) = 16 := by
  simp only [eZero, bPoly, eTail_residue, tThree, fTail_residue, hTail_residue, avg, Ring.inverse_eq_inv, avgDen_two, inv2, inv3, inv5, inv27, inv24, inv4, inv14]
  decide +kernel

theorem eOne_residue : eOne (2 : F) = 8 := by
  simp only [eOne, bPoly, eTail_residue, tThree, fTail_residue, hTail_residue, avg, Ring.inverse_eq_inv, avgDen_two, inv2, inv3, inv5, inv27, inv24, inv4, inv14]
  decide +kernel

theorem beta_residue : beta (2 : F) = 27 := by
  simp only [beta, tThree_zero_residue, vCubic, Ring.inverse_eq_inv, avgDen_two, inv2, inv3, inv5, inv27, inv24, inv4, inv14]
  decide +kernel

theorem cNu_residue : cNu (2 : F) = 9 := by
  simp only [cNu, vCubic]
  decide +kernel

theorem hU_residue : hU (2 : F) = 25 := by
  simp only [hU, eZero_residue, qC_residue]
  decide +kernel

theorem hV_residue : hV (2 : F) = 1 := by
  simp only [hV, eZero_residue, eOne_residue, qC_residue, qL_residue]
  decide +kernel

theorem hW_residue : hW (2 : F) = 20 := by
  simp only [hW, eOne_residue, qC_residue]
  decide +kernel

theorem hhU_residue : hhU (2 : F) = 8 := by
  simp only [hhU, headPhi, eTail_residue, vCubic, beta_residue, tThree,
    fTail_residue, hTail_residue, avg, Ring.inverse_eq_inv, avgDen_two, inv2, inv3, inv5, inv27, inv24, inv4, inv14]
  decide +kernel

theorem hhV_residue : hhV (2 : F) = 9 := by
  simp only [hhV, headPhi, eTail_residue, vCubic, beta_residue, tThree,
    fTail_residue, hTail_residue, avg, Ring.inverse_eq_inv, avgDen_two, inv2, inv3, inv5, inv27, inv24, inv4, inv14]
  decide +kernel

theorem hhW_residue : hhW (2 : F) = 5 := by
  simp only [hhW, headPhi, eTail_residue, vCubic, beta_residue, tThree,
    fTail_residue, hTail_residue, avg, Ring.inverse_eq_inv, avgDen_two, inv2, inv3, inv5, inv27, inv24, inv4, inv14]
  decide +kernel

theorem determinant_residue : determinant (2 : F) = 14 := by
  simp only [determinant, hU_residue, hV_residue, hhV_residue, hhU_residue]
  decide +kernel

theorem headSum_residue : headSum (2 : F) = 2 := by
  simp only [headSum, hV_residue, hW_residue, hhV_residue, hhW_residue, determinant_residue,
    Ring.inverse_eq_inv, avgDen_two, inv2, inv3, inv5, inv27, inv24, inv4, inv14]
  decide +kernel

theorem headProduct_residue : headProduct (2 : F) = 17 := by
  simp only [headProduct, hW_residue, hU_residue, hhU_residue, hhW_residue, determinant_residue,
    Ring.inverse_eq_inv, avgDen_two, inv2, inv3, inv5, inv27, inv24, inv4, inv14]
  decide +kernel

theorem head_residue : (headQuadratic (2 : F)).eval 11 = 0 ∧
    (headQuadratic (2 : F)).eval 20 = 0 := by
  simp only [eval_headQuadratic, headSum_residue, headProduct_residue]
  decide +kernel

theorem head_derivative_residue : (headQuadratic (2 : F)).derivative.eval 11 = 20 ∧
    (headQuadratic (2 : F)).derivative.eval 20 = 9 := by
  simp only [eval_derivative_headQuadratic, headSum_residue]
  decide +kernel

section Lift

variable {R : Type*} [CommRing R] (ρ : R →+* F) [IsLocalHom ρ]

private theorem unit_of_residue {z : R} (h : ρ z ≠ 0) : IsUnit z :=
  IsUnit.of_map ρ z (isUnit_iff_ne_zero.mpr h)

/-- The actual (uncancelled) denominators used by the scalar head solve. -/
def PaidHead (c : R) : Prop :=
    IsUnit (avgDen : R) ∧ IsUnit (2 : R) ∧ IsUnit (3 : R) ∧ IsUnit (5 : R) ∧
    IsUnit c ∧ IsUnit (hDen c) ∧ IsUnit (fDen c) ∧ IsUnit (eDen c) ∧
    IsUnit (tThree c 0) ∧ IsUnit (determinant c) ∧ IsUnit (cNu c)

theorem paidHead_of_residue {c : R} (hc : ρ c = 2) : PaidHead c := by
  refine ⟨unit_of_residue ρ ?_,unit_of_residue ρ ?_,unit_of_residue ρ ?_,
    unit_of_residue ρ ?_,unit_of_residue ρ ?_,unit_of_residue ρ ?_,
    unit_of_residue ρ ?_,unit_of_residue ρ ?_,unit_of_residue ρ ?_,
    unit_of_residue ρ ?_,unit_of_residue ρ ?_⟩
  all_goals
    simp only [map_natCast, map_ofNat, hc, map_hDen, hDen_residue, map_fDen, fDen_residue,
      map_eDen, eDen_residue, map_tThree, map_zero, tThree_zero_residue,
      map_determinant, determinant_residue, map_cNu, cNu_residue]
    decide +kernel

theorem head_other_root {c a : R} (ha : (headQuadratic c).eval a = 0) :
    (headQuadratic c).eval (headSum c-a) = 0 := by
  rw [eval_headQuadratic] at ha ⊢
  convert ha using 1; ring

/-- A simple-root lifting operation, stated separately from any analytic model. -/
def SimpleLift : Prop :=
  ∀ (P : Polynomial R) (a : F),
    (P.map ρ).eval a = 0 →
    (P.map ρ).derivative.eval a ≠ 0 →
    ∃ x : R, P.eval x = 0 ∧ ρ x = a

/-- Two Hensel operations give the actual ordered head roots, their tail
residues, and all uncancelled scalar head guards. It does not prove the physical
Runge–Kutta order equations or the later nonlinear closure conditions. -/
theorem scalar_existence (hlift : SimpleLift ρ) :
    ∃ c a b : R,
      (decic R).eval c = 0 ∧ ρ c = 2 ∧
      (headQuadratic c).eval a = 0 ∧ ρ a = 11 ∧
      (headQuadratic c).eval b = 0 ∧ ρ b = 20 ∧ b = headSum c-a ∧
      ρ (hTail c) = 22 ∧ ρ (fTail c) = 7 ∧ ρ (eTail c) = 27 ∧ PaidHead c := by
  have hc0 : ((decic R).map ρ).eval (2:F) = 0 := by rw [map_decic, decic_residue]
  have hc1 : ((decic R).map ρ).derivative.eval (2:F) ≠ 0 := by
    rw [map_decic, decic_derivative_residue]
    decide +kernel
  obtain ⟨c, hc, hcR⟩ := hlift (decic R) 2 hc0 hc1
  have hqc : (headQuadratic c).map ρ = headQuadratic (2 : F) := by rw [map_headQuadratic, hcR]
  have ha0 : ((headQuadratic c).map ρ).eval (11:F) = 0 := by rw [hqc]; exact head_residue.1
  have ha1 : ((headQuadratic c).map ρ).derivative.eval (11:F) ≠ 0 := by
    rw [hqc, head_derivative_residue.1]
    decide +kernel
  obtain ⟨a, ha, haR⟩ := hlift (headQuadratic c) 11 ha0 ha1
  have hbR : ρ (headSum c-a) = 20 := by
    simp only [map_sub, map_headSum, hcR, headSum_residue, haR]
    decide +kernel
  exact ⟨c,a,headSum c-a,hc,hcR,ha,haR,head_other_root ha,hbR,rfl,
    by simp [hcR, hTail_residue], by simp [hcR, fTail_residue], by simp [hcR, eTail_residue],
    paidHead_of_residue ρ hcR⟩

end Lift
end RKResearch.Certified.ERK10FixedQ29Adic

#print axioms RKResearch.Certified.ERK10FixedQ29Adic.avg_integer_moments
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.head_derivative_residue
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.paidHead_of_residue
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.scalar_existence
