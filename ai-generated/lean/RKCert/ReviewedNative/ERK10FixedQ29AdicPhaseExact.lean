module

public import RKCert.ReviewedNative.ERK10FixedQ29AdicHeadExact
public import RKCert.ReviewedNative.ERK10FixedQ29AdicPhaseCheck0
public import RKCert.ReviewedNative.ERK10FixedQ29AdicPhaseCheck1
public import RKCert.ReviewedNative.ERK10FixedQ29AdicPhaseCheck2
public import RKCert.ReviewedNative.ERK10FixedQ29AdicPhaseCheck3
public import RKCert.ReviewedNative.ERK10FixedQ29AdicPhaseCheck4
public import RKCert.ReviewedNative.ERK10FixedQ29AdicPhaseCheck5
public import RKCert.ReviewedNative.ERK10FixedQ29AdicPhaseCheck6
public import RKCert.ReviewedNative.ERK10FixedQ29AdicPhaseCheck7
public import RKCert.ReviewedNative.ERK10FixedQ29AdicPhaseCheck8
public import RKCert.ReviewedNative.ERK10FixedQ29AdicPhaseCheck9

@[expose] public section

namespace RKResearch.Certified.ERK10FixedQ29Adic.Nonlinear
open Packed Polynomial
open scoped Ring BigOperators

set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem Dreceipt (i : ℕ) (hi : i<8) :
    Form.check (denD0) (digitsD0) (exprD i) (repD i) = true := by
  interval_cases i
  · exact certD0
  · exact certD1
  · exact certD2
  · exact certD3
  · exact certD4
  · exact certD5
  · exact certD6
  · exact certD7

theorem Mreceipt (i : ℕ) (hi : i<7) :
    Form.check (denM0) (digitsM0) (exprM i) (repM i) = true := by
  interval_cases i
  · exact certM0
  · exact certM1
  · exact certM2
  · exact certM3
  · exact certM4
  · exact certM5
  · exact certM6

def denMuIdx : ℕ → ℕ
  | 0 => denMu0
  | 1 => denMu1
  | 2 => denMu2
  | 3 => denMu3
  | 4 => denMu4
  | 5 => denMu5
  | 6 => denMu6
  | _ => 1

def digitsMuIdx : ℕ → ℕ
  | 0 => digitsMu0
  | 1 => digitsMu1
  | 2 => digitsMu2
  | 3 => digitsMu3
  | 4 => digitsMu4
  | 5 => digitsMu5
  | 6 => digitsMu6
  | _ => 1

theorem Mureceipt (i : ℕ) (hi : i<7) :
    Form.check (denMuIdx i) (digitsMuIdx i) (exprMu i) (repMu i) = true := by
  interval_cases i
  · exact certMu0
  · exact certMu1
  · exact certMu2
  · exact certMu3
  · exact certMu4
  · exact certMu5
  · exact certMu6

section Exact
variable {R : Type*} [CommRing R] (ρ : R →+* F) [IsLocalHom ρ] (c : R)
variable (hp : (decic R).eval c = 0) (hr : ρ c = 2)
include ρ hp hr

theorem exactD (i : ℕ) (hi : i<8) : (repD i).val c = actualD c i := by
  rw [Form.check_sound ρ hp (Dreceipt i hi)]
  simp [exprD,val_coeffD,map_tailFive,actualD,exactE ρ c hp hr,exactF ρ c hp hr,exactH ρ c hp hr,
    exactS ρ c hp hr,exactQ ρ c hp hr]

theorem exactM (i : ℕ) (hi : i<7) : (repM i).val c = actualM c i := by
  rw [Form.check_sound ρ hp (Mreceipt i hi),exprM,actualM]
  apply avgForm_val
  intro y
  simp

theorem exactMu (i : ℕ) (hi : i<7) : (repMu i).val c = muCoeff c i := by
  rw [Form.check_sound ρ hp (Mureceipt i hi),exprMu,muCoeff,Form.val_sumFin]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs with hh
  · have hm : j.val-1-i<7 := by have := j.isLt; omega
    simp only [Form.val_mul,Form.val,exactD ρ c hp hr j.val j.isLt,exactM ρ c hp hr _ hm]
  · simp

theorem exactMuF (y : Form) : (muF y).val c = muValue c (y.val c) := by
  rw [muF,muValue,Form.val_sumFin]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Form.val_mul,Form.val_pow,Form.val,exactMu ρ c hp hr i.val i.isLt]

theorem exactCNu : repCNu.val c = cNu c := by
  rw [Form.check_sound ρ hp certCNu]
  simp [exprCNu,cNu,vCubicF_exact c]

private theorem exactPhase (y : Form) (v : Rep)
    (hy : IsUnit (y.val c)) (hz : (phaseF y v).val c = 0) :
    v.val c = phaseValue c (y.val c) := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,hν⟩ := paidHead_of_residue ρ hr
  have hv : (y.val c*cNu c)*v.val c = -(muValue c (y.val c)*vCubic c (y.val c)) := by
    apply eq_neg_of_add_eq_zero_left
    simpa [phaseF,exactCNu ρ c hp hr,exactMuF ρ c hp hr,vCubicF_exact c] using hz
  have hu := hy.mul hν
  apply hu.mul_left_cancel
  rw [hv,phaseValue,mul_left_comm,Ring.mul_inverse_cancel _ hu,mul_one]

omit hp in
private theorem paidF : IsUnit (fTail c) := by
  apply IsUnit.of_map ρ
  apply isUnit_iff_ne_zero.mpr
  rw [map_fTail,hr,fTail_residue]
  decide +kernel

omit hp in
private theorem paidH : IsUnit (hTail c) := by
  apply IsUnit.of_map ρ
  apply isUnit_iff_ne_zero.mpr
  rw [map_hTail,hr,hTail_residue]
  decide +kernel

omit hp hr in
private theorem paidG : IsUnit (6:R) := by
  apply IsUnit.of_map ρ
  apply isUnit_iff_ne_zero.mpr
  rw [map_ofNat]
  decide +kernel

theorem exactPhaseF : repPhaseF.val c = phaseValue c (fTail c) := by
  have hz : (phaseF (fr repF) repPhaseF).val c = 0 := by
    simpa only [exprPhaseF,repZero_val] using (Form.check_sound ρ hp certPhaseF).symm
  have hy : IsUnit ((fr repF).val c) := by simpa [exactF ρ c hp hr] using paidF ρ c hr
  simpa [exactF ρ c hp hr] using exactPhase ρ c hp hr _ _ hy hz

theorem exactPhaseG : repPhaseG.val c = phaseValue c 6 := by
  have hz : (phaseF 6 repPhaseG).val c = 0 := by
    simpa only [exprPhaseG,repZero_val] using (Form.check_sound ρ hp certPhaseG).symm
  have hy : IsUnit ((6:Form).val c) := by simpa using paidG ρ
  simpa using exactPhase ρ c hp hr _ _ hy hz

theorem exactPhaseH : repPhaseH.val c = phaseValue c (hTail c) := by
  have hz : (phaseF (fr repH) repPhaseH).val c = 0 := by
    simpa only [exprPhaseH,repZero_val] using (Form.check_sound ρ hp certPhaseH).symm
  have hy : IsUnit ((fr repH).val c) := by simpa [exactH ρ c hp hr] using paidH ρ c hr
  simpa [exactH ρ c hp hr] using exactPhase ρ c hp hr _ _ hy hz

theorem exact_phase_alignment :
    (phaseValue c (hTail c)-phaseValue c (fTail c))*(6-fTail c) =
      (phaseValue c 6-phaseValue c (fTail c))*(hTail c-fTail c) := by
  apply sub_eq_zero.mp
  have hz := (Form.check_sound ρ hp certAligned).symm
  simpa [exprAligned,exactPhaseH ρ c hp hr,exactPhaseF ρ c hp hr,exactPhaseG ρ c hp hr,
    exactF ρ c hp hr,exactH ρ c hp hr] using hz

omit hp in
theorem paid_gap : IsUnit (6-fTail c) := by
  apply IsUnit.of_map ρ
  apply isUnit_iff_ne_zero.mpr
  simp only [map_sub,map_ofNat,map_fTail,hr,fTail_residue]
  decide +kernel

theorem exact_h_phase :
    phaseIntercept c + phaseSlope c*hTail c = phaseValue c (hTail c) := by
  have hu := paid_gap ρ c hr
  have hsl : (6-fTail c)*phaseSlope c = phaseValue c 6-phaseValue c (fTail c) := by
    rw [phaseSlope,mul_left_comm,Ring.mul_inverse_cancel _ hu,mul_one]
  apply hu.mul_left_cancel
  calc
    _ = (6-fTail c)*phaseValue c (fTail c) +
        ((6-fTail c)*phaseSlope c)*(hTail c-fTail c) := by unfold phaseIntercept; ring
    _ = _ := by rw [hsl,←exact_phase_alignment ρ c hp hr]; ring

end Exact
end RKResearch.Certified.ERK10FixedQ29Adic.Nonlinear

#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Nonlinear.exact_phase_alignment
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Nonlinear.exact_h_phase
