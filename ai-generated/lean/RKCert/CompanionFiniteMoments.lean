module

public import RKCert.CompanionFiniteAxes

@[expose] public section

/-! # Executable small-factor moments without symbolic polynomial reduction -/
namespace RKCert.Compound
open Polynomial
open scoped Classical
variable {R : Type*} [CommRing R]

noncomputable def scaledMomentLinear (M j d : ℕ) (u : R) : R[X] →ₗ[R] R where
  toFun := scaledMoment M j d u
  map_add' v w := by
    simp only [scaledMoment,coeff_add,mul_add,Finset.sum_add_distrib]
  map_smul' a v := by
    simp only [RingHom.id_apply,smul_eq_C_mul,scaledMoment,coeff_C_mul,smul_eq_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

@[simp] theorem scaledMomentLinear_apply (M j d : ℕ) (u : R) (P : R[X]) :
    scaledMomentLinear M j d u P=scaledMoment M j d u P := rfl

private theorem scaledMoment_cap_succ (M j d : ℕ) (u : R) (P : R[X]) (hd : P.natDegree≤d) :
    scaledMoment M j (d+1) u P=scaledMoment M j d u P := by
  unfold scaledMoment
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc,Fin.val_last,coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_of_le hd),
    mul_zero,add_zero]

private theorem scaledMoment_mul_X (M j d : ℕ) (u : R) (P : R[X]) :
    scaledMoment M j (d+1) u (X*P)=u*scaledMoment M (j+1) d u P := by
  unfold scaledMoment
  rw [Fin.sum_univ_succ,Finset.mul_sum]
  simp only [Fin.val_zero,coeff_X_mul_zero,mul_zero,zero_add,Fin.val_succ,coeff_X_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [show j+(i.val+1)+1=j+1+i.val+1 by omega,pow_succ]
  ring

/-- The normalized, integer-cleared moment of a list of linear factors.
The only divisions in the executable form are exact natural quotients
of the prechosen factorial. -/
def smallFactorMoment (M : ℕ) (u : R) : ℕ → List R → R
  | j, [] => ((M/(j+1):ℕ):R)
  | j, a::w => u*smallFactorMoment M u (j+1) w-a*smallFactorMoment M u j w

noncomputable def linearFactors (w : List R) : R[X] :=
  (w.map fun a => X-C a).prod

theorem linearFactors_degree (w : List R) : (linearFactors w).natDegree≤w.length := by
  induction w with
  | nil => simp [linearFactors]
  | cons a w ih =>
    have z : linearFactors (a::w)=(X-C a)*linearFactors w := rfl
    rw [z,List.length_cons]
    exact natDegree_mul_le.trans <| (Nat.add_le_add (natDegree_X_sub_C_le a) ih).trans_eq (Nat.add_comm _ _)

theorem smallFactorMoment_exact (M j : ℕ) (u : R) (w : List R) :
    smallFactorMoment M u j w=scaledMoment M j w.length u (linearFactors w) := by
  induction w generalizing j with
  | nil => simp [smallFactorMoment,linearFactors,scaledMoment]
  | cons a w ih =>
    simp only [smallFactorMoment,ih,List.length_cons]
    change _=scaledMoment M j (w.length+1) u ((X-C a)*linearFactors w)
    rw [sub_mul,←smul_eq_C_mul]
    let L := scaledMomentLinear M j (w.length+1) u
    change _=L (X*linearFactors w-a • linearFactors w)
    rw [map_sub,map_smul,smul_eq_mul]
    change _=scaledMoment M j (w.length+1) u (X*linearFactors w)-
      a*scaledMoment M j (w.length+1) u (linearFactors w)
    rw [scaledMoment_mul_X,scaledMoment_cap_succ M j w.length u _ (linearFactors_degree _)]

end RKCert.Compound
