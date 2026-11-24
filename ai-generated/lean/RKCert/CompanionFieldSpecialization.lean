module

public import RKCert.CompanionRawSingularity

@[expose] public section

/-! # Specialization at an actual possibly nonmonic pencil and factor -/
namespace RKCert.Compound
open Polynomial RKCert.Paired.Signature
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
theorem eq_C_mul_normalize (P : K[X]) (P0 : P≠0) :
    P=C P.leadingCoeff*normalize P := by
  rw [normalize_apply,coe_normUnit_of_ne_zero P0]
  have l0 := leadingCoeff_ne_zero.mpr P0
  have unit : C P.leadingCoeff*C P.leadingCoeff⁻¹=1 := by
    rw [←map_mul,mul_inv_cancel₀ l0,map_one]
  calc
    P=P*1 := (mul_one _).symm
    _ = P*(C P.leadingCoeff*C P.leadingCoeff⁻¹) := by rw [unit]
    _ = _ := by ring

omit [CharZero K] in
theorem normalize_eq_inv_smul (P : K[X]) (P0 : P≠0) :
    normalize P=P.leadingCoeff⁻¹ • P := by
  rw [normalize_apply,coe_normUnit_of_ne_zero P0,smul_eq_C_mul,mul_comm]

theorem normalize_weighted_moment (P : K[X]) (P0 : P≠0) (u : K) (j w : ℕ) :
    paidMoment ((1-X)^w*normalize P) u j =
      P.leadingCoeff⁻¹*paidMoment ((1-X)^w*P) u j := by
  simp only [←weightedMomentLinear_apply,normalize_eq_inv_smul P P0,map_smul,smul_eq_mul]

theorem rawMomentNorm_specialized_zero {n k M j w : ℕ} (q V : K[X]) (q0 : q≠0) (V0 : V≠0)
    (qn : q.natDegree=n) (d : V.natDegree=k) (dvd : V∣q)
    (u : K) (un : u≠0) (den : ∀ l : Fin (k+w+1),j+l.val+1∣M)
    (zero : paidMoment ((1-X)^w*V) u j=0) :
    rawMomentNorm (n:=n) k M j w u (fun t => q.coeff t.val)=0 := by
  let P := normalize q
  let G := normalize V
  have pn : P.natDegree=n := natDegree_normalize.trans qn
  have gn : G.natDegree=k := natDegree_normalize.trans d
  rw [←pn,←gn]
  have cd : G∣P := (normalize_dvd_iff).mpr (dvd_normalize_iff.mpr dvd)
  refine rawMomentNorm_zero_of_factor P (monic_normalize q0) G (monic_normalize V0) cd _ ?_ M j w u un ?_ ?_
  · intro i
    change q.coeff i.val=q.coeff P.natDegree*P.coeff i.val
    have pd : P.natDegree=q.natDegree := pn.trans qn.symm
    have key : q.coeff P.natDegree=q.leadingCoeff :=
      (congrArg (fun j : ℕ => q.coeff j) pd).trans coeff_natDegree
    rw [key]
    exact (congrArg (fun W : K[X] => W.coeff i.val) (eq_C_mul_normalize q q0)).trans
      (coeff_C_mul _)
  · rwa [gn]
  · dsimp only [G]
    rw [normalize_weighted_moment V V0,zero,mul_zero]

theorem rawGramNorm_specialized_zero {n k M j w : ℕ} (q V : K[X]) (q0 : q≠0) (V0 : V≠0)
    (qn : q.natDegree=n) (d : V.natDegree=k) (dvd : V∣q)
    (u : K) (un : u≠0) (den : ∀ c≤2,∀ l : Fin (k+w+1),j+c+l.val+1∣M)
    (zero : paidMoment ((1-X)^w*V) u j*paidMoment ((1-X)^w*V) u (j+2)-
      (paidMoment ((1-X)^w*V) u (j+1))^2=0) :
    rawGramNorm (n:=n) k M j w u (fun t => q.coeff t.val)=0 := by
  let P := normalize q
  let G := normalize V
  have pn : P.natDegree=n := natDegree_normalize.trans qn
  have gn : G.natDegree=k := natDegree_normalize.trans d
  rw [←pn,←gn]
  have cd : G∣P := (normalize_dvd_iff).mpr (dvd_normalize_iff.mpr dvd)
  refine rawGramNorm_zero_of_factor P (monic_normalize q0) G (monic_normalize V0) cd _ ?_ M j w u un ?_ ?_
  · intro i
    change q.coeff i.val=q.coeff P.natDegree*P.coeff i.val
    have pd : P.natDegree=q.natDegree := pn.trans qn.symm
    have key : q.coeff P.natDegree=q.leadingCoeff :=
      (congrArg (fun j : ℕ => q.coeff j) pd).trans coeff_natDegree
    rw [key]
    exact (congrArg (fun W : K[X] => W.coeff i.val) (eq_C_mul_normalize q q0)).trans
      (coeff_C_mul _)
  · intro c c2
    rw [gn]
    exact den c c2
  · dsimp only [G]
    simp only [normalize_weighted_moment V V0]
    linear_combination (V.leadingCoeff⁻¹)^2*zero

end
end RKCert.Compound
