module

public import RKCert.ReviewedNative.ERK10FixedQ29AdicMarked

@[expose] public section

namespace RKResearch.Certified.ERK10FixedQ29Adic.Physical
open PaidBarycentric Nonlinear Packed Polynomial
open scoped Ring BigOperators Polynomial

noncomputable section
set_option maxRecDepth 40000
set_option maxHeartbeats 0

variable {R : Type*} [CommRing R]

/-- The actual cofactor scale set by the first live ordinary row. -/
def actualScale (x : Site→R) : R :=
  -(score x headA*(x headA)^2*Den ordinary x headA)*(2:R)⁻¹ʳ

def actualQ (c : R) (x : Site→R) : Polynomial R :=
  C ((actualScale x)⁻¹ʳ)*normQuad c

def headK (c b : R) : R := c*(2*c-4*b)⁻¹ʳ
def bOverA (a b : R) : R := b*a⁻¹ʳ
def cOverA (c a : R) : R := c*a⁻¹ʳ
def headDelta (c a b : R) : R :=
  3*bOverA a b*headK c b-2*cOverA c a*headK c b+cOverA c a

def centerRatio (c a b : R) : R :=
  let k := headK c b
  let s := bOverA a b
  let t := cOverA c a
  (-2)*(2*s*t*k^2+2*s*t*k-2*s*k^2+s*k-2*t*k+t)*(c^2*headDelta c a b)⁻¹ʳ

def uResidues : Site→F := ![0,0,18,23,25,7,11,5,17,9,1]
def etaResidues : Site→F := ![0,0,16,6,0,2,15,3,8,21,1]

private theorem eval6 (z:R) : (6:Polynomial R).eval z=6 := by simp
private theorem eval15 (z:R) : (15:Polynomial R).eval z=15 := by simp

private theorem rinv2 : (2:F)⁻¹ʳ=15 := by rw [Ring.inverse_eq_inv]; decide +kernel
private theorem rinv9 : (9:F)⁻¹ʳ=13 := by rw [Ring.inverse_eq_inv]; decide +kernel
private theorem rinv27 : (27:F)⁻¹ʳ=14 := by rw [Ring.inverse_eq_inv]; decide +kernel

theorem field_u_cross : ∀ i : Site, i∈ordinary →
    Den ordinary nodeResidues i*uResidues i=27 := by decide +kernel

theorem field_eta_read : ∀ i : Site, i∈withoutCenter →
    -( (nodeResidues i-1)*vCubic (2:F) (nodeResidues i)*13+
      3*((nodeResidues i-15)*(nodeResidues i-7)*(nodeResidues i-6)*(nodeResidues i-22)))=
      etaResidues i := by
  unfold vCubic
  decide +kernel

theorem field_lambda_read : -(∑ i∈withoutCenter, etaResidues i*uResidues i)=11 := by
  decide +kernel

open RKCert.ReviewedNative.IntegerHornerCertificate
private theorem read_rep {a : Rep} {r : F}
    (hp : Packed.Paid a.den) (h : coeval a.num (2:F)=(a.den:F)*r) :
    a.val (2:F)=r := by
  have hu := paid_unit (RingHom.id F) hp
  exact hu.mul_left_cancel ((a.den_mul_val _ hu).trans h)

theorem field_gamma : repGamma.val (2:F)=2 := by
  apply read_rep <;> decide +kernel

theorem field_phiF : repPhaseF.val (2:F)=1 := by
  apply read_rep <;> decide +kernel

theorem field_phiG : repPhaseG.val (2:F)=18 := by
  apply read_rep <;> decide +kernel

section Actual

variable (ρ : R →+* F) [IsLocalHom ρ] (c a b : R)
variable (hp : (decic R).eval c=0) (hc : ρ c=2) (ha : ρ a=11) (hb : ρ b=20)
include ρ hp hc ha hb

omit hp in
theorem actual_scale_residue : ρ (actualScale (nodal c a b))=27 := by
  have hn := nodes_reduce ρ c a b hc ha hb
  have hnA : ρ (nodal c a b headA)=nodeResidues headA := congrFun hn headA
  rw [actualScale,map_mul,map_neg,map_mul,map_mul,map_pow,map_ringInverse,map_ofNat,
    map_score,map_den,hn,hnA,field_score,rinv2]
  decide +kernel

omit hp in
theorem actual_scale_unit : IsUnit (actualScale (nodal c a b)) := by
  apply IsUnit.of_map ρ
  apply isUnit_iff_ne_zero.mpr
  rw [actual_scale_residue ρ c a b hc ha hb]
  decide +kernel

omit hp in
theorem actual_u_residue {i : Site} (hi : i∈ordinary) :
    ρ (uAggregate (nodal c a b) (actualScale (nodal c a b)) i)=uResidues i := by
  have hd := den_unit (paid_residue_sites ordinary) hi
  have hact := den_unit (actual_paid_sites ρ c a b hc ha hb ordinary) hi
  apply hd.mul_left_cancel
  have hh : Den ordinary (nodal c a b) i *
      uAggregate (nodal c a b) (actualScale (nodal c a b)) i=actualScale (nodal c a b) := by
    rw [uAggregate,ordInv,mul_left_comm,Ring.mul_inverse_cancel _ hact,mul_one]
  have H := congrArg ρ hh
  rw [map_mul,map_den,nodes_reduce ρ c a b hc ha hb,actual_scale_residue ρ c a b hc ha hb] at H
  exact H.trans (field_u_cross i hi).symm

omit ha hb in
theorem sigma_gamma : (gap c*cNu c)*closureSigma c = repGamma.val c := by
  have hu := ResiduePivot.paidB0 ρ c hp hc
  have hEq := congrArg (fun p : Polynomial R => p.coeff 0) (exact_remainder_scale ρ c hp hc)
  simp only [coeff_add,coeff_C_mul,coeff_zero] at hEq
  have hE := eq_neg_of_add_eq_zero_left hEq
  have hB : (bRemainder c).coeff 0*closureSigma c = -((eRemainder c).coeff 0) := by
    rw [closureSigma,mul_left_comm,Ring.mul_inverse_cancel _ hu,mul_one]
  apply hu.mul_left_cancel
  calc
    _ = (gap c*cNu c)*((bRemainder c).coeff 0*closureSigma c) := by ring
    _ = _ := by rw [hB,mul_neg,hE,neg_neg];ring

omit ha hb in
theorem actual_sigma_residue : ρ (closureSigma c)=3 := by
  have h := congrArg ρ (sigma_gamma ρ c hp hc)
  rw [map_mul,map_mul,gap,map_sub,map_ofNat,map_fTail,hc,fTail_residue,
    map_cNu,hc,cNu_residue,ResiduePivot.mapRep,hc,field_gamma] at h
  have hκ : ((6:F)-7)*9=20 := by decide +kernel
  rw [hκ] at h
  have hu : IsUnit (20:F) := isUnit_iff_ne_zero.mpr (by decide +kernel)
  exact hu.mul_left_cancel (h.trans (by decide +kernel))

theorem actual_eta_residue {i : Site} (hi : i∈withoutCenter) :
    ρ (etaNoncenter (closureU c) (nodal c a b) i)=etaResidues i := by
  have hni : ρ (nodal c a b i)=nodeResidues i := congrFun (nodes_reduce ρ c a b hc ha hb) i
  simp only [etaNoncenter,closureU,actualU0,actualT4_factor,eval_add,eval_mul,eval_sub,eval_X,
    eval_one,eval_C,eval6,eval15,actualV_eval,map_neg,map_add,map_mul,map_sub,map_one,map_ofNat,
    map_ringInverse,map_vCubic,map_cNu,map_fTail,map_hTail,
    hc,hni,cNu_residue,fTail_residue,hTail_residue,
    rinv9,actual_sigma_residue ρ c hp hc]
  exact field_eta_read i hi

theorem actual_lambda_residue :
    ρ (splitLambda (closureU c) (nodal c a b) (actualScale (nodal c a b)))=11 := by
  rw [splitLambda,map_neg,map_sum]
  have hh : (∑ i∈withoutCenter, ρ (etaNoncenter (closureU c) (nodal c a b) i *
      uAggregate (nodal c a b) (actualScale (nodal c a b)) i)) =
      ∑ i∈withoutCenter, etaResidues i*uResidues i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_mul, actual_eta_residue ρ c a b hp hc ha hb hi,
      actual_u_residue ρ c a b hc ha hb (split_sites i hi).1]
  rw [hh,field_lambda_read]

omit ha hb in
theorem actual_phiF_residue : ρ (phaseValue c (fTail c))=1 := by
  rw [←exactPhaseF ρ c hp hc,ResiduePivot.mapRep,hc,field_phiF]

omit ha hb in
theorem actual_phiG_residue : ρ (phaseValue c 6)=18 := by
  rw [←exactPhaseG ρ c hp hc,ResiduePivot.mapRep,hc,field_phiG]

omit ha hb in
theorem actual_slope_residue : ρ (phaseSlope c)=12 := by
  simp only [phaseSlope,map_mul,map_sub,map_ringInverse,map_ofNat,map_fTail,hc,fTail_residue,
    actual_phiF_residue ρ c hp hc,actual_phiG_residue ρ c hp hc,Ring.inverse_eq_inv]
  decide +kernel

omit ha hb in
theorem actual_intercept_residue : ρ (phaseIntercept c)=4 := by
  simp only [phaseIntercept,map_sub,map_mul,map_fTail,hc,fTail_residue,
    actual_phiF_residue ρ c hp hc,actual_slope_residue ρ c hp hc]
  decide +kernel

theorem actual_Qc_residue : ρ ((actualQ c (nodal c a b)).eval c)=8 := by
  simp only [actualQ,normQuad,eval_mul,eval_C,eval_sub,eval_X,eval15,actualQ1_eval,
    map_mul,map_ringInverse,map_sub,map_add,map_ofNat,hc,actual_scale_residue ρ c a b hc ha hb,
    actual_intercept_residue ρ c hp hc,actual_slope_residue ρ c hp hc,rinv27]
  decide +kernel

omit hp ha in
theorem actual_k_residue : ρ (headK c b)=16 := by
  simp only [headK,map_mul,map_sub,map_ringInverse,map_ofNat,hc,hb,Ring.inverse_eq_inv]
  decide +kernel

omit hp hc in
theorem actual_ba_residue : ρ (bOverA a b)=15 := by
  simp only [bOverA,map_mul,map_ringInverse,ha,hb,Ring.inverse_eq_inv]
  decide +kernel

omit hp hb in
theorem actual_ca_residue : ρ (cOverA c a)=16 := by
  simp only [cOverA,map_mul,map_ringInverse,hc,ha,Ring.inverse_eq_inv]
  decide +kernel

omit hp in
theorem actual_delta_residue : ρ (headDelta c a b)=21 := by
  simp only [headDelta,map_mul,map_sub,map_add,map_ofNat,actual_k_residue ρ c b hc hb,
    actual_ba_residue ρ a b ha hb,actual_ca_residue ρ c a hc ha]
  decide +kernel

omit hp in
theorem actual_Lc_residue : ρ (centerRatio c a b)=8 := by
  simp only [centerRatio,map_mul,map_sub,map_add,map_neg,map_pow,map_ofNat,map_ringInverse,
    hc,actual_k_residue ρ c b hc hb,actual_ba_residue ρ a b ha hb,
    actual_ca_residue ρ c a hc ha,actual_delta_residue ρ c a b hc ha hb,Ring.inverse_eq_inv]
  decide +kernel

omit hp in
theorem actual_head_denominator_units :
    IsUnit a ∧ IsUnit (2*c-4*b) ∧ IsUnit (c^2*headDelta c a b) := by
  refine ⟨IsUnit.of_map ρ _ (isUnit_iff_ne_zero.mpr ?_),
    IsUnit.of_map ρ _ (isUnit_iff_ne_zero.mpr ?_),
    IsUnit.of_map ρ _ (isUnit_iff_ne_zero.mpr ?_)⟩
  · rw [ha]; decide +kernel
  · simp only [map_sub,map_mul,map_ofNat,hc,hb]; decide +kernel
  · simp only [map_mul,map_pow,hc,actual_delta_residue ρ c a b hc ha hb]; decide +kernel

end Actual
end
end RKResearch.Certified.ERK10FixedQ29Adic.Physical

#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.actual_scale_unit
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.actual_eta_residue
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.actual_lambda_residue
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.actual_Qc_residue
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.actual_Lc_residue
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.actual_head_denominator_units
