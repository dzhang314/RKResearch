module

public import RKCert.CompanionScaledMoment

@[expose] public section

/-! # Exact constant-factor exceptions require no prime computation -/
namespace RKCert.FixedPolynomial
open Polynomial RKCert.Paired.Signature
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

theorem no_weighted_constant_moments {V : K[X]} (V0 : V≠0) (d : V.natDegree=0)
    {u : K} (un : u≠0) (j w : ℕ) (w1 : w≤1)
    (p : paidMoment ((1-X)^w*V) u j=0)
    (q : paidMoment ((1-X)^w*V) u (j+1)=0) : False := by
  have wD : ((1-X : K[X])^w).natDegree≤w := by
    exact (natDegree_pow_le_of_le w ((natDegree_sub_le _ _).trans (by simp))).trans_eq (Nat.mul_one w)
  have bd : ((1-X)^w*V).natDegree≤1 := natDegree_mul_le.trans (by rw [d,Nat.add_zero]; omega)
  have e := RKCert.Paired.primitive_shift_detect ((1-X)^w*V) bd u un (k:=j) (fun i => ?_)
  · have ne : (1-X:K[X])≠0 := by
      intro z
      have h : (1:K[X])=X := sub_eq_zero.mp z
      exact Nat.zero_ne_one (by simpa using congrArg natDegree h)
    exact (mul_ne_zero (pow_ne_zero _ ne) V0) e
  · have h : i.val=0 ∨ i.val=1 := by have _:=i.isLt; omega
    rcases h with h|h
    · simpa only [h,Nat.add_zero,paidMoment] using p
    · simpa only [h,paidMoment] using q

private theorem constant_moment_formula (V : K[X]) (d : V.natDegree=0) (u : K) (j : ℕ) :
    paidMoment V u j=V.coeff 0*u^(j+1)/((j+1:ℕ):K) := by
  have h := RKCert.Paired.primitive_eval_power_mul V u j d.le
  simpa [paidMoment] using h

theorem constant_gram_nonzero {V : K[X]} (V0 : V≠0) (d : V.natDegree=0)
    {u : K} (un : u≠0) (j : ℕ) :
    paidMoment V u j*paidMoment V u (j+2)-(paidMoment V u (j+1))^2≠0 := by
  have cz : V.coeff 0≠0 := by
    intro c
    exact V0 (by rw [eq_C_of_natDegree_le_zero d.le,c,map_zero])
  let z : K := (j:K)+1
  have z0 : z≠0 := by
    change (j:K)+1≠0
    exact_mod_cast (show j+1≠0 by omega)
  have z1 : z+1≠0 := by
    change (j:K)+1+1≠0
    exact_mod_cast (show j+1+1≠0 by omega)
  have z2 : z+2≠0 := by
    change (j:K)+1+2≠0
    exact_mod_cast (show j+1+2≠0 by omega)
  have scale : (z*(z+2))⁻¹-((z+1)^2)⁻¹≠0 := by
    intro h
    field_simp [z0,z1,z2] at h
    have one : (1:K)=0 := by linear_combination h
    exact one_ne_zero one
  have ex : u^(j+1)*u^(j+2+1)=(u^(j+1+1))^2 := by
    rw [←pow_add,←pow_mul]
    congr 1
    omega
  have d1 : ((j+1+1:ℕ):K)=z+1 := by simp [z]
  have d2 : ((j+2+1:ℕ):K)=z+2 := by simp [z]; ring
  have d0 : ((j+1:ℕ):K)=z := by simp [z]
  rw [constant_moment_formula V d,constant_moment_formula V d,constant_moment_formula V d,
    d0,d1,d2,div_mul_div_comm,div_pow]
  have pp : V.coeff 0*u^(j+1)*(V.coeff 0*u^(j+2+1)) =
      V.coeff 0^2*(u^(j+1)*u^(j+2+1)) := by ring
  rw [pp,ex,mul_pow]
  have factor : V.coeff 0^2*(u^(j+1+1))^2/(z*(z+2)) -
      V.coeff 0^2*(u^(j+1+1))^2/(z+1)^2 =
      (V.coeff 0^2*(u^(j+1+1))^2)*((z*(z+2))⁻¹-((z+1)^2)⁻¹) := by
    rw [div_eq_mul_inv,div_eq_mul_inv,mul_sub]
  rw [factor]
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ cz) (pow_ne_zero _ (pow_ne_zero _ un))) scale

end
end RKCert.FixedPolynomial
