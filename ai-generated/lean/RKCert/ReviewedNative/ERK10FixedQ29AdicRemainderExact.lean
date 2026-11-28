module

public import RKCert.ReviewedNative.ERK10FixedQ29AdicRemainderCheck0
public import RKCert.ReviewedNative.ERK10FixedQ29AdicRemainderCheck1
public import RKCert.ReviewedNative.ERK10FixedQ29AdicRemainderCheck2
public import RKCert.ReviewedNative.ERK10FixedQ29AdicRemainderCheck3

@[expose] public section

namespace RKResearch.Certified.ERK10FixedQ29Adic.Nonlinear
open Packed Polynomial
open scoped Ring BigOperators Polynomial

noncomputable section
set_option maxRecDepth 40000
set_option maxHeartbeats 0

theorem remReceipt (i : ℕ) (hi : i<11) :
    Form.check denRemainder digitsRemainder (exprRemainder i) repZero = true := by
  interval_cases i
  · exact certRem0
  · exact certRem1
  · exact certRem2
  · exact certRem3
  · exact certRem4
  · exact certRem5
  · exact certRem6
  · exact certRem7
  · exact certRem8
  · exact certRem9
  · exact certRem10

section Unconditional
variable {R : Type*} [CommRing R]

theorem vCoordsF_map (c : R) : vCoordsF.map (Form.val c) = vCoords c := by
  simp [vCoordsF,vCoords]

theorem map_tailFour (x : R) (r f g h : Form) :
    (tailFour r f g h).map (Form.val x) =
    tailFour (r.val x) (f.val x) (g.val x) (h.val x) := by
  simp [tailFour,map_polyLin]

theorem quotCoeff_exact (c : R) (i : ℕ) :
    (quotCoordsF[i]?.getD 0).val c = (actualQuot c).coeff i := by
  simp [val_getD, quotCoordsF, actualQuot, coeff_fromCoeffs]

theorem actualQ1_eval (c y : R) :
    (actualQ1 c).eval y = phaseIntercept c+phaseSlope c*y := by
  simp [actualQ1,fromCoeffs]

theorem modByMonic_C_mul [Nontrivial R] (a : R) (p q : Polynomial R)
    (hq : q.Monic) : (C a*p) %ₘ q = C a*(p %ₘ q) := by
  have h1 : C a*(p %ₘ q)+q*(C a*(p /ₘ q))=C a*p := by
    calc
      _ = C a*((p %ₘ q)+q*(p /ₘ q)) := by ring
      _ = _ := by rw [modByMonic_add_div]
  have h2 : (C a*(p %ₘ q)).degree < q.degree := by
    calc
      _ ≤ (C a).degree + (p %ₘ q).degree := degree_mul_le _ _
      _ ≤ 0 + (p %ₘ q).degree := add_le_add degree_C_le le_rfl
      _ = (p %ₘ q).degree := zero_add _
      _ < _ := degree_modByMonic_lt _ hq
  exact (div_modByMonic_unique _ _ hq ⟨h1,h2⟩).2

end Unconditional

section Exact
variable {R : Type*} [CommRing R] (ρ : R →+* F) [IsLocalHom ρ] (c : R)
variable (hp : (decic R).eval c = 0) (hr : ρ c = 2)
include ρ hp hr

theorem exactD_all (i : ℕ) : (repD i).val c = (actualD7 c).coeff i := by
  by_cases hi : i<8
  · rw [coeff_actualD7]
    exact exactD ρ c hp hr i hi
  · have hGe : i = (i-8)+8 := by omega
    have hrep : repD i = repZero := (congrArg repD hGe).trans rfl
    rw [hrep,repZero_val,coeff_eq_zero_of_natDegree_lt ((natDegreeD7 c).trans_lt (by omega))]

theorem exactMu_all (i : ℕ) : (repMu i).val c = (actualMu c).coeff i := by
  by_cases hi : i<7
  · rw [coeff_mu_low c hi]
    exact exactMu ρ c hp hr i hi
  · have hGe : i = (i-7)+7 := by omega
    have hrep : repMu i = repZero := (congrArg repMu hGe).trans rfl
    rw [hrep,repZero_val,coeff_eq_zero_of_natDegree_lt ((natDegreeMu c).trans_lt (by omega))]

theorem t4CoordsF_map :
    t4CoordsF.map (Form.val c) = tailFour 15 (fTail c) 6 (hTail c) := by
  simp [t4CoordsF,map_tailFour,exactF ρ c hp hr,exactH ρ c hp hr]

theorem qnCoordsF_map : qnCoordsF.map (Form.val c) = qnCoords c := by
  simp [qnCoordsF,qnCoords,gap,phaseDiff,exactF ρ c hp hr,
    exactPhaseF ρ c hp hr,exactPhaseG ρ c hp hr]

theorem exactUC_coeff (i : ℕ) : (uCoeffF i).val c = (actualUC c).coeff i := by
  rw [actualUC,coeff_add,coeff_C_mul,coeff_C_mul,actualV,coeff_X_sub_one_fromCoeffs,
    actualT4,coeff_fromCoeffs]
  simp [uCoeffF,val_getD,t4CoordsF_map ρ c hp hr,vCoordsF_map,gap,exactF ρ c hp hr]

theorem exactSecond_coeff (i : ℕ) :
    (secondCoeffF i).val c = (actualSecond c).coeff i := by
  simp [secondCoeffF,actualSecond,coeff_C_mul,actualQn,
    coeff_X_one_sub_X_fromCoeffs,val_getD,qnCoordsF_map ρ c hp hr,exactCNu ρ c hp hr]

theorem exactRem_coeff (i : ℕ) :
    (exprRemainder i).val c = (actualLHS c-actualD7 c*actualQuot c).coeff i := by
  simp only [exprRemainder,actualLHS,coeff_sub,coeff_mul_fin,Form.val_sub,Form.val_sumFin,
    Form.val_mul,Form.val,exactD_all ρ c hp hr,exactMu_all ρ c hp hr,
    quotCoeff_exact,exactUC_coeff ρ c hp hr,exactSecond_coeff ρ c hp hr]

/-- A homogeneous exact polynomial identity at the selected decic root.
The quotient is certified, not obtained by an unchecked field simplifier. -/
theorem exact_homogeneous_divisibility : actualLHS c = actualD7 c*actualQuot c := by
  ext i
  by_cases hi : i<11
  · apply sub_eq_zero.mp
    rw [←coeff_sub,←exactRem_coeff ρ c hp hr i]
    simpa only [repZero_val] using (Form.check_sound ρ hp (remReceipt i hi)).symm
  · have hd : (actualD7 c*actualQuot c).natDegree ≤ 10 :=
      (natDegree_mul_le ..).trans (Nat.add_le_add (natDegreeD7 c) (natDegreeQuot c))
    rw [coeff_eq_zero_of_natDegree_lt ((natDegreeLHS c).trans_lt (by omega)),
      coeff_eq_zero_of_natDegree_lt (hd.trans_lt (by omega))]

omit hp in
theorem scaled_q1 : C (gap c)*actualQ1 c = actualQn c := by
  have hu : IsUnit (gap c) := paid_gap ρ c hr
  have hu' : IsUnit (6-fTail c) := hu
  have hs : gap c*phaseSlope c = phaseDiff c := by
    unfold phaseSlope phaseDiff gap
    rw [mul_left_comm, Ring.mul_inverse_cancel _ hu',mul_one]
  have ht : gap c*phaseIntercept c = gap c*phaseValue c (fTail c)-phaseDiff c*fTail c := by
    unfold phaseIntercept
    rw [mul_sub,←mul_assoc,hs]
  unfold actualQ1 actualQn qnCoords
  rw [←ht,←hs]
  simp only [fromCoeffs, C_0, mul_zero, add_zero, map_mul]
  ring

omit hp in
theorem lhs_as_remainder_scale :
    actualLHS c = C (gap c*cNu c)*(actualMu c*actualU0 c-X*(1-X)*actualQ1 c) +
      C (repGamma.val c)*(actualMu c*actualT4 c) := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,hν⟩ := paidHead_of_residue ρ hr
  have eqU : C (gap c*cNu c)*actualU0 c = C (gap c)*((X-1)*actualV c) := by
    have hC : C (gap c*cNu c)*C ((cNu c)⁻¹ʳ) = C (gap c) := by
      rw [←map_mul,mul_assoc,Ring.mul_inverse_cancel _ hν,mul_one]
    unfold actualU0
    calc
      _ = (C (gap c*cNu c)*C ((cNu c)⁻¹ʳ))*((X-1)*actualV c) := by ring
      _ = _ := by rw [hC]
  have eqQ : C (gap c*cNu c)*actualQ1 c = C (cNu c)*actualQn c := by
    rw [←scaled_q1 ρ c hr,map_mul]
    ring
  symm
  calc
    _ = actualMu c*(C (gap c*cNu c)*actualU0 c+C (repGamma.val c)*actualT4 c) -
        X*(1-X)*(C (gap c*cNu c)*actualQ1 c) := by ring
    _ = actualLHS c := by rw [eqU,eqQ]; unfold actualLHS actualUC actualSecond; ring

theorem exact_remainder_scale :
    C (gap c*cNu c)*eRemainder c+C (repGamma.val c)*bRemainder c = 0 := by
  haveI := ρ.domain_nontrivial
  have hf : (actualLHS c) %ₘ (actualD7 c) = 0 := by
    exact (modByMonic_eq_zero_iff_dvd (monicD7 c)).mpr ⟨actualQuot c,exact_homogeneous_divisibility ρ c hp hr⟩
  rw [lhs_as_remainder_scale ρ c hr,add_modByMonic,
    modByMonic_C_mul _ _ _ (monicD7 c),modByMonic_C_mul _ _ _ (monicD7 c)] at hf
  exact hf

/-- The seven actual remainder proportionalities, in fact for every
coefficient by the degree bound. The unit pivot is established separately. -/
theorem exact_remainder_proportionality (i : ℕ) :
    (eRemainder c).coeff i*(bRemainder c).coeff 0 =
      (bRemainder c).coeff i*(eRemainder c).coeff 0 := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,hν⟩ := paidHead_of_residue ρ hr
  have hu : IsUnit (gap c*cNu c) := (paid_gap ρ c hr).mul hν
  have ht (j : ℕ) : (gap c*cNu c)*(eRemainder c).coeff j =
      -(repGamma.val c*(bRemainder c).coeff j) := by
    have H := congrArg (fun p : Polynomial R => p.coeff j) (exact_remainder_scale ρ c hp hr)
    apply eq_neg_of_add_eq_zero_left
    simpa only [coeff_add,coeff_C_mul,coeff_zero] using H
  apply hu.mul_left_cancel
  calc
    _ = ((gap c*cNu c)*(eRemainder c).coeff i)*(bRemainder c).coeff 0 := by ring
    _ = (bRemainder c).coeff i*((gap c*cNu c)*(eRemainder c).coeff 0) := by rw [ht i,ht 0]; ring
    _ = _ := by ring

end Exact
end
end RKResearch.Certified.ERK10FixedQ29Adic.Nonlinear

#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Nonlinear.exact_homogeneous_divisibility
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Nonlinear.exact_remainder_scale
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Nonlinear.exact_remainder_proportionality
