module

public import RKCert.ReviewedNative.ERK10FixedQ29AdicHeadCheck0
public import RKCert.ReviewedNative.ERK10FixedQ29AdicHeadCheck1
public import RKCert.ReviewedNative.ERK10FixedQ29AdicHeadCheck2
public import RKCert.ReviewedNative.ERK10FixedQ29AdicHeadCheck3
public import RKCert.ReviewedNative.ERK10FixedQ29AdicHeadCheck4

@[expose] public section

namespace RKResearch.Certified.ERK10FixedQ29Adic.Nonlinear

open Packed
open scoped Ring
set_option maxRecDepth 40000
set_option maxHeartbeats 0

section Exact
variable {R : Type*} [CommRing R] (ρ : R →+* F) [IsLocalHom ρ] (c : R)
variable (hp : (decic R).eval c = 0) (hr : ρ c = 2)
include ρ hp hr

theorem exactH : repH.val c = hTail c := by
  have hz := (Form.check_sound ρ hp certH).symm
  have he : hDP c*repH.val c = hNP c := by
    apply sub_eq_zero.mp
    simpa [exprH, hNP, hDP] using hz
  have hd : IsUnit (hDP c) := by
    apply IsUnit.of_map ρ
    apply isUnit_iff_ne_zero.mpr
    have hv : ρ (hDP c) = hDP (2:F) := by simp [hDP,hr,map_ofNat]
    rw [hv,hDP_residue]
    decide +kernel
  exact hd.mul_left_cancel (he.trans (h_clear c (paidHead_of_residue ρ hr)).symm)

theorem exactF : repF.val c = fTail c := by
  have hz := (Form.check_sound ρ hp certF).symm
  have he : fDP c*repF.val c = fNP c := by
    apply sub_eq_zero.mp
    simpa [exprF, fNP, fDP] using hz
  have hd : IsUnit (fDP c) := by
    apply IsUnit.of_map ρ
    apply isUnit_iff_ne_zero.mpr
    have hv : ρ (fDP c) = fDP (2:F) := by simp [fDP,hr,map_ofNat]
    rw [hv,fDP_residue]
    decide +kernel
  exact hd.mul_left_cancel (he.trans (f_clear c (paidHead_of_residue ρ hr)).symm)

theorem exactE : repE.val c = eTail c := by
  obtain ⟨_,_,_,_,_,_,_,he,_,_,_⟩ := paidHead_of_residue ρ hr
  have hz := (Form.check_sound ρ hp certE).symm
  have hex : eDen c*repE.val c = c*(c-26) := by
    apply sub_eq_zero.mp
    simpa [exprE,eDen,omegaPoly] using hz
  apply he.mul_left_cancel
  rw [hex,eTail,mul_left_comm, Ring.mul_inverse_cancel _ he,mul_one]

theorem tThreeF_exact (y : Form) :
    (tThreeF y).val c = tThree c (y.val c) := by
  simp [tThreeF,tThree,exactF ρ c hp hr,exactH ρ c hp hr]

theorem bPolyF_exact (y : Form) :
    (bPolyF y).val c = bPoly c (y.val c) := by
  simp [bPolyF,bPoly,exactE ρ c hp hr,tThreeF_exact ρ c hp hr]

omit ρ hp hr in
theorem vCubicF_exact (y : Form) :
    (vCubicF y).val c = vCubic c (y.val c) := by
  simp [vCubicF,vCubic]

theorem exactK : repK.val c = kMom c := by
  rw [Form.check_sound ρ hp certK,exprK,kMom]
  apply avgForm_val
  intro y
  simp [tThreeF_exact ρ c hp hr]

theorem exactQC : repQC.val c = qC c := by
  rw [Form.check_sound ρ hp certQC]
  simp [exprQC,qC,exactE ρ c hp hr,exactK ρ c hp hr]

theorem exactE0 : repE0.val c = eZero c := by
  rw [Form.check_sound ρ hp certE0,exprE0,eZero]
  apply avgForm_val
  intro y
  simp [bPolyF_exact ρ c hp hr]

theorem exactE1 : repE1.val c = eOne c := by
  rw [Form.check_sound ρ hp certE1,exprE1,eOne]
  apply avgForm_val
  intro y
  simp [bPolyF_exact ρ c hp hr]

theorem exactBeta : repBeta.val c = beta c := by
  obtain ⟨_,_,_,_,_,_,_,_,ht,_,_⟩ := paidHead_of_residue ρ hr
  have hz := (Form.check_sound ρ hp certBeta).symm
  have hex : tThree c 0*repBeta.val c = vCubic c 0 := by
    apply sub_eq_zero.mp
    simpa [exprBeta,tThreeF_exact ρ c hp hr,vCubicF_exact c] using hz
  apply ht.mul_left_cancel
  rw [hex,beta,mul_left_comm, Ring.mul_inverse_cancel _ ht,mul_one]

theorem phiF_exact (y : Form) :
    (phiF y).val c = headPhi c (y.val c) := by
  simp [phiF,headPhi,exactE ρ c hp hr,exactBeta ρ c hp hr,
    tThreeF_exact ρ c hp hr,vCubicF_exact c]

theorem exactUU : repUU.val c = hhU c := by
  rw [Form.check_sound ρ hp certUU,exprUU,hhU]
  simp only [Form.val_neg]
  congr 1
  apply avgForm_val
  intro y
  simp [phiF_exact ρ c hp hr]

theorem exactVV : repVV.val c = hhV c := by
  rw [Form.check_sound ρ hp certVV,exprVV,hhV]
  apply avgForm_val
  intro y
  exact phiF_exact ρ c hp hr y

theorem exactWW : repWW.val c = hhW c := by
  rw [Form.check_sound ρ hp certWW,exprWW,hhW]
  apply avgForm_val
  intro y
  simp [phiF_exact ρ c hp hr]

theorem qL_eq_negative : qL c = -qC c := by
  have hz := origin_zero_of_decic ρ hr hp
  have hl : lMom c = -kMom c := by
    calc
      _ = origin c-kMom c := by unfold origin; ring
      _ = _ := by rw [hz,zero_sub]
  rw [qL,qC,hl,mul_neg]

theorem exactU : repU.val c = hU c := by
  rw [Form.check_sound ρ hp certU]
  simp [exprU,hU,exactE0 ρ c hp hr,exactQC ρ c hp hr]

theorem exactV : repV.val c = hV c := by
  rw [Form.check_sound ρ hp certV]
  simp [exprV,hV,exactE0 ρ c hp hr,exactE1 ρ c hp hr,exactQC ρ c hp hr,qL_eq_negative ρ c hp hr]

theorem exactW : repW.val c = hW c := by
  rw [Form.check_sound ρ hp certW]
  simp [exprW,hW,exactE1 ρ c hp hr,exactQC ρ c hp hr]

theorem exactDet : repDet.val c = determinant c := by
  rw [Form.check_sound ρ hp certDet]
  simp [exprDet,determinant,exactU ρ c hp hr,exactV ρ c hp hr,exactUU ρ c hp hr,exactVV ρ c hp hr]

theorem exactS : repS.val c = headSum c := by
  obtain ⟨_,_,_,_,_,_,_,_,_,hd,_⟩ := paidHead_of_residue ρ hr
  have hz := (Form.check_sound ρ hp certS).symm
  have hex : determinant c*repS.val c = hV c*hhW c-hW c*hhV c := by
    apply sub_eq_zero.mp
    simpa [exprS,exactDet ρ c hp hr,exactV ρ c hp hr,exactW ρ c hp hr,
      exactVV ρ c hp hr,exactWW ρ c hp hr] using hz
  apply hd.mul_left_cancel
  rw [hex,headSum,mul_left_comm,Ring.mul_inverse_cancel _ hd,mul_one]

theorem exactQ : repQ.val c = headProduct c := by
  obtain ⟨_,_,_,_,_,_,_,_,_,hd,_⟩ := paidHead_of_residue ρ hr
  have hz := (Form.check_sound ρ hp certQ).symm
  have hex : determinant c*repQ.val c = hW c*hhU c-hU c*hhW c := by
    apply sub_eq_zero.mp
    simpa [exprQ,exactDet ρ c hp hr,exactU ρ c hp hr,exactW ρ c hp hr,
      exactUU ρ c hp hr,exactWW ρ c hp hr] using hz
  apply hd.mul_left_cancel
  rw [hex,headProduct,mul_left_comm,Ring.mul_inverse_cancel _ hd,mul_one]

end Exact
end RKResearch.Certified.ERK10FixedQ29Adic.Nonlinear

#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Nonlinear.exactS
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Nonlinear.exactQ
