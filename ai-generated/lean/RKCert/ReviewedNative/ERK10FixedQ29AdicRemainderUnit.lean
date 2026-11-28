module

public import RKCert.ReviewedNative.ERK10FixedQ29AdicRemainderExact

@[expose] public section

namespace RKResearch.Certified.ERK10FixedQ29Adic.Nonlinear
open Packed Polynomial
open scoped Ring BigOperators Polynomial

noncomputable section
set_option maxRecDepth 40000
set_option maxHeartbeats 0

namespace ResiduePivot

def dMod : Polynomial F := fromCoeffs [2,21,10,25,26,4,26,1]
def muMod : Polynomial F := fromCoeffs [16,16,7,22,7,10,22]
def t4Mod : Polynomial F := fromCoeffs [27,14,12,8,1]
def qMod : Polynomial F := fromCoeffs [11,4,20,22]
def bMod : Polynomial F := fromCoeffs [4,11,23,1,25,10,6]

theorem dMod_nd : dMod.natDegree ≤ 7 := natDegree_fromCoeffs _
theorem muMod_nd : muMod.natDegree ≤ 6 := natDegree_fromCoeffs _
theorem t4Mod_nd : t4Mod.natDegree ≤ 4 := natDegree_fromCoeffs _
theorem qMod_nd : qMod.natDegree ≤ 3 := natDegree_fromCoeffs _
theorem bMod_nd : bMod.natDegree ≤ 6 := natDegree_fromCoeffs _
theorem dMod_monic : dMod.Monic := by
  apply monic_of_natDegree_le_of_coeff_eq_one 7 dMod_nd
  rw [dMod,coeff_fromCoeffs]
  rfl

theorem dMod_deg : dMod.degree = 7 := by
  apply degree_eq_of_le_of_coeff_ne_zero (degree_le_of_natDegree_le dMod_nd)
  rw [dMod,coeff_fromCoeffs]
  decide +kernel

theorem field_identity : bMod+dMod*qMod = muMod*t4Mod := by
  ext i
  by_cases hi : i<11
  · interval_cases i
    all_goals
      simp only [bMod,dMod,qMod,muMod,t4Mod,coeff_add,coeff_mul_fin,coeff_fromCoeffs]
      decide +kernel
  · have hd : (dMod*qMod).natDegree≤10 :=
      (natDegree_mul_le ..).trans (Nat.add_le_add dMod_nd qMod_nd)
    have hL : (bMod+dMod*qMod).natDegree≤10 :=
      (natDegree_add_le ..).trans (max_le (bMod_nd.trans (by decide)) hd)
    have hR : (muMod*t4Mod).natDegree≤10 :=
      (natDegree_mul_le ..).trans (Nat.add_le_add muMod_nd t4Mod_nd)
    rw [coeff_eq_zero_of_natDegree_lt (hL.trans_lt (by omega)),
      coeff_eq_zero_of_natDegree_lt (hR.trans_lt (by omega))]

theorem field_mod : (muMod*t4Mod) %ₘ dMod = bMod := by
  refine (div_modByMonic_unique qMod bMod dMod_monic ⟨field_identity,?_⟩).2
  rw [dMod_deg]
  exact (degree_le_of_natDegree_le bMod_nd).trans_lt (by decide)

open RKCert.ReviewedNative.IntegerHornerCertificate
private theorem residue_cross (a : Rep) (r : F)
    (hp : Paid a.den) (h : coeval a.num (2:F) = (a.den:F)*r) : a.val (2:F) = r := by
  have hu : IsUnit (a.den:F) := paid_unit (RingHom.id F) hp
  exact hu.mul_left_cancel ((a.den_mul_val _ hu).trans h)

theorem repD_mod (i : ℕ) : (repD i).val (2:F) = dMod.coeff i := by
  by_cases hi : i<8
  · interval_cases i
    all_goals
      rw [dMod,coeff_fromCoeffs]
      apply residue_cross
      <;> decide +kernel
  · have H : repD i=repZero := (congrArg repD (show i=(i-8)+8 by omega)).trans rfl
    rw [H,repZero_val,coeff_eq_zero_of_natDegree_lt (dMod_nd.trans_lt (by omega))]

theorem repMu_mod (i : ℕ) : (repMu i).val (2:F) = muMod.coeff i := by
  by_cases hi : i<7
  · interval_cases i
    all_goals
      rw [muMod,coeff_fromCoeffs]
      apply residue_cross
      <;> decide +kernel
  · have H : repMu i=repZero := (congrArg repMu (show i=(i-7)+7 by omega)).trans rfl
    rw [H,repZero_val,coeff_eq_zero_of_natDegree_lt (muMod_nd.trans_lt (by omega))]

section Maps
variable {R : Type*} [CommRing R] (ρ : R →+* F) [IsLocalHom ρ] (c : R)
variable (hp : (decic R).eval c = 0) (hr : ρ c = 2)
include ρ hp hr

omit hp hr in
private theorem map_coeval (a : List ℤ) : ρ (coeval a c) = coeval a (ρ c) := by
  induction a with
  | nil => simp [coeval,horner]
  | cons a as ih => simp only [coeval_cons,map_add,map_mul,map_intCast,ih]

omit hp hr in
theorem mapRep (a : Rep) : ρ (a.val c) = a.val (ρ c) := by
  simp only [Rep.val,map_mul,map_ringInverse,map_natCast,map_coeval]

theorem mapD7 : (actualD7 c).map ρ = dMod := by
  ext i
  rw [coeff_map,←exactD_all ρ c hp hr, mapRep,hr,repD_mod]

theorem mapMu : (actualMu c).map ρ = muMod := by
  ext i
  rw [coeff_map,←exactMu_all ρ c hp hr,mapRep,hr,repMu_mod]

omit hp hr in
private theorem map_fromCoeffs (a : List R) :
    (fromCoeffs a).map ρ = fromCoeffs (a.map ρ) := by
  induction a with
  | nil => simp [fromCoeffs]
  | cons a as ih => simp [fromCoeffs,Polynomial.map_add,Polynomial.map_mul,ih]

omit hp in
theorem mapT4 : (actualT4 c).map ρ = t4Mod := by
  rw [actualT4,map_fromCoeffs,t4Mod]
  apply congrArg fromCoeffs
  simp only [tailFour,polyLin,List.map_cons,List.map_nil,map_sub,map_mul,map_zero,map_one,
    map_ofNat,map_fTail,map_hTail,hr,fTail_residue,hTail_residue]
  decide +kernel

theorem residueB0 : ρ ((bRemainder c).coeff 0) = 4 := by
  rw [←coeff_map,bRemainder,map_modByMonic ρ (monicD7 c),Polynomial.map_mul,
    mapD7 ρ c hp hr,mapMu ρ c hp hr,mapT4 ρ c hr,field_mod,bMod,coeff_fromCoeffs]
  rfl

theorem paidB0 : IsUnit ((bRemainder c).coeff 0) := by
  apply IsUnit.of_map ρ
  apply isUnit_iff_ne_zero.mpr
  rw [residueB0 ρ c hp hr]
  decide +kernel

end Maps
end ResiduePivot

section Closure
variable {R : Type*} [CommRing R]

def closureSigma (c : R) : R :=
  -((eRemainder c).coeff 0)*((bRemainder c).coeff 0)⁻¹ʳ

def closureU (c : R) : Polynomial R := actualU0 c + C (closureSigma c)*actualT4 c

variable (ρ : R →+* F) [IsLocalHom ρ] (c : R)
variable (hp : (decic R).eval c = 0) (hr : ρ c = 2)
include ρ hp hr

theorem closure_remainder_zero :
    (actualMu c*closureU c-X*(1-X)*actualQ1 c) %ₘ actualD7 c = 0 := by
  letI : Nontrivial R := ρ.domain_nontrivial
  have hB := ResiduePivot.paidB0 ρ c hp hr
  have hscale : (bRemainder c).coeff 0*closureSigma c = -(eRemainder c).coeff 0 := by
    rw [closureSigma,mul_left_comm,Ring.mul_inverse_cancel _ hB,mul_one]
  have ha : eRemainder c+C (closureSigma c)*bRemainder c = 0 := by
    ext i
    rw [coeff_add,coeff_C_mul,coeff_zero]
    apply hB.mul_left_cancel
    calc
      _ = (eRemainder c).coeff i*(bRemainder c).coeff 0 +
           ((bRemainder c).coeff 0*closureSigma c)*(bRemainder c).coeff i := by ring
      _ = _ := by rw [exact_remainder_proportionality ρ c hp hr i,hscale,mul_zero]; ring
  have hb : actualMu c*closureU c-X*(1-X)*actualQ1 c =
      (actualMu c*actualU0 c-X*(1-X)*actualQ1 c)+
      C (closureSigma c)*(actualMu c*actualT4 c) := by
    unfold closureU
    ring
  rw [hb,add_modByMonic,modByMonic_C_mul _ _ _ (monicD7 c)]
  exact ha

omit hp in
theorem closure_host :
    (closureU c).eval 15 = -1 := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,hν⟩ := paidHead_of_residue ρ hr
  have ht : (actualT4 c).eval 15 = 0 := by
    rw [actualT4_factor]
    simp
  have hu : (actualU0 c).eval 15 = -1 := by
    have H : (15-1)*vCubic c 15 = -(cNu c) := by unfold cNu; ring
    rw [actualU0,eval_mul,eval_mul,eval_sub,eval_X,eval_one,actualV_eval,eval_C,H,
      neg_mul,Ring.mul_inverse_cancel _ hν]
  rw [closureU,eval_add,eval_mul,ht,mul_zero,add_zero,hu]

omit ρ hr hp in
theorem closure_degree : (closureU c).natDegree ≤ 4 := by
  have hX : (X-1:Polynomial R).natDegree≤1 :=
    (natDegree_sub_le ..).trans (max_le natDegree_X_le (by simp))
  have hU : (actualU0 c).natDegree≤4 := by
    unfold actualU0
    rw [mul_comm _ (C _)]
    exact (natDegree_C_mul_le ..).trans ((natDegree_mul_le ..).trans (Nat.add_le_add hX (natDegreeV c)))
  have hT := (natDegree_C_mul_le (closureSigma c) (actualT4 c)).trans (natDegreeT4 c)
  unfold closureU
  exact (natDegree_add_le ..).trans (max_le hU hT)

end Closure
end
end RKResearch.Certified.ERK10FixedQ29Adic.Nonlinear

#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Nonlinear.ResiduePivot.paidB0
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Nonlinear.closure_remainder_zero
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Nonlinear.closure_host
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Nonlinear.closure_degree
