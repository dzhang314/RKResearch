module

public import RKCert.ERKOrderNineFiveSixOffPlacement

@[expose] public section

/-! # Four exact quadratic pseudo-division steps -/
namespace RKCert.Paired
open Polynomial
variable {K : Type*} [Field K]

/-- One declared-degree cancellation. The four-step map below is
polynomial in all coefficients even when the head coefficient is zero. -/
noncomputable def quadraticPremStep (P : K[X]) (n : ℕ) : K[X] →ₗ[K] K[X] where
  toFun U := C (P.coeff 2)*U - C (U.coeff n)*(X^(n-2)*P)
  map_add' U V := by simp only [coeff_add,map_add]; ring
  map_smul' a U := by simp only [RingHom.id_apply,smul_eq_C_mul,coeff_C_mul,map_mul]; ring

theorem quadraticPremStep_apply (P U : K[X]) (n : ℕ) :
    quadraticPremStep P n U = C (P.coeff 2)*U - C (U.coeff n)*(X^(n-2)*P) := rfl

theorem quadraticPremStep_lower {P U : K[X]} {n : ℕ}
    (hn : 2≤n) (dP : P.natDegree=2) (dU : U.natDegree≤n) :
    (quadraticPremStep P n U).natDegree≤n-1 := by
  have xP : (X^(n-2)*P).natDegree≤n := by
    have e := natDegree_mul_le_of_le (natDegree_X_pow_le (R:=K) (n-2)) dP.le
    exact e.trans (by omega)
  have a : (quadraticPremStep P n U).natDegree≤n := by
    rw [quadraticPremStep_apply]
    have h₁ : (C (P.coeff 2)*U).natDegree≤n := (natDegree_C_mul_le _ _).trans dU
    have h₂ : (C (U.coeff n)*(X^(n-2)*P)).natDegree≤n := (natDegree_C_mul_le _ _).trans xP
    simpa only [max_self] using natDegree_sub_le_of_le h₁ h₂
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  by_cases h : i=n
  · subst i
    rw [quadraticPremStep_apply,coeff_sub,coeff_C_mul,coeff_C_mul,
      coeff_X_pow_mul',ite_eq_left (by omega),show n-(n-2)=2 by omega]
    ring
  · exact coeff_eq_zero_of_natDegree_lt (by omega)

theorem quadraticPremStep_dvd {P U : K[X]} (n : ℕ) (div : P∣U) :
    P∣quadraticPremStep P n U := by
  obtain ⟨R,e⟩ := div
  refine ⟨C (P.coeff 2)*R-C (U.coeff n)*X^(n-2),?_⟩
  rw [quadraticPremStep_apply]
  nth_rw 1 [e]
  ring

noncomputable def quadraticPrem5 (P : K[X]) : K[X] →ₗ[K] K[X] :=
  (quadraticPremStep P 2).comp ((quadraticPremStep P 3).comp
    ((quadraticPremStep P 4).comp (quadraticPremStep P 5)))

theorem quadraticPrem5_degree {P U : K[X]} (dP : P.natDegree=2) (dU : U.natDegree≤5) :
    (quadraticPrem5 P U).natDegree≤1 := by
  change (quadraticPremStep P 2 (quadraticPremStep P 3
    (quadraticPremStep P 4 (quadraticPremStep P 5 U)))).natDegree≤1
  exact quadraticPremStep_lower (by decide) dP (quadraticPremStep_lower (by decide) dP
    (quadraticPremStep_lower (by decide) dP (quadraticPremStep_lower (by decide) dP dU)))

theorem quadraticPrem5_zero_of_dvd {P U : K[X]} (dP : P.natDegree=2) (dU : U.natDegree≤5)
    (div : P∣U) : quadraticPrem5 P U=0 := by
  have e := quadraticPrem5_degree dP dU
  by_contra nn
  have h : P∣quadraticPrem5 P U := quadraticPremStep_dvd 2 (quadraticPremStep_dvd 3
    (quadraticPremStep_dvd 4 (quadraticPremStep_dvd 5 div)))
  have f := natDegree_le_of_dvd h nn
  omega

noncomputable def quadraticPremDet (P U V : K[X]) : K :=
  (quadraticPrem5 P U).coeff 0*(quadraticPrem5 P V).coeff 1 -
    (quadraticPrem5 P U).coeff 1*(quadraticPrem5 P V).coeff 0

/-- The exact determinant of the two polynomial remainders vanishes
under the stronger actual divisibility certificate. -/
theorem quadraticPremDet_zero_of_dvd {P U V : K[X]} {a : K}
    (dP : P.natDegree=2) (dU : U.natDegree≤5) (dV : V.natDegree≤5)
    (div : P∣V-C a*U) : quadraticPremDet P U V=0 := by
  have dv : (V-C a*U).natDegree≤5 :=
    natDegree_sub_le_of_le dV ((natDegree_C_mul_le _ _).trans dU)
  have e := quadraticPrem5_zero_of_dvd dP dv div
  rw [←smul_eq_C_mul,map_sub,map_smul,sub_eq_zero,smul_eq_C_mul] at e
  unfold quadraticPremDet
  rw [e,coeff_C_mul,coeff_C_mul]
  ring

end RKCert.Paired
