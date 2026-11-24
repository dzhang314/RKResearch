module

public import RKCert.Dirk15PencilDispatch

@[expose] public section

/-! # Exact integer Jacobi representatives for the three arithmetic obligations

The positive leading coefficient agrees with the fixed-prime replay.
The free parameter is only rescaled between monic and integer pencils;
no parameter of the actual array is specialized. -/
namespace RKCert.FixedPolynomial
open Polynomial RKCert.Paired
open scoped Classical
noncomputable section

def integerJacobi (n : ℕ) : ℤ[X] :=
  C ((-1:ℤ)^(n+1))*(shiftedLegendre (n+1)).derivative

theorem integerJacobi_coeff (n k : ℕ) :
    (integerJacobi n).coeff k=(-1:ℤ)^(n+k+2)*(k+1)*
      ((n+1).choose (k+1))*((n+k+2).choose (k+1)) := by
  rw [integerJacobi,coeff_C_mul,coeff_derivative,coeff_shiftedLegendre,
    Nat.choose_symm_of_eq_add (show n+1+(k+1)=n+1+(k+1) by rfl),
    show n+k+2=n+1+(k+1) by omega,pow_add (-1:ℤ) (n+1) (k+1)]
  ring

theorem integerJacobi_degree (n : ℕ) : (integerJacobi n).natDegree=n := by
  rw [integerJacobi,natDegree_C_mul (pow_ne_zero _ (by decide)),
    natDegree_derivative,natDegree_shiftedLegendre]
  omega

private theorem low_reflection (n : ℕ) :
    (-1:ℤ[X])^n*((shiftedLegendre (n+1)).derivative.comp (1-X)) =
      (shiftedLegendre (n+1)).derivative := by
  have h := congrArg derivative (neg_one_pow_mul_shiftedLegendre_comp_one_sub_X_eq (n+1))
  rw [show ((-1:ℤ[X])^(n+1))=C ((-1:ℤ)^(n+1)) by simp,derivative_C_mul,
    derivative_comp_one_sub_X] at h
  have e : C ((-1:ℤ)^(n+1))*(-((shiftedLegendre (n+1)).derivative.comp (1-X))) =
      (-1:ℤ[X])^n*((shiftedLegendre (n+1)).derivative.comp (1-X)) := by
    rw [pow_succ,map_mul]
    simp
  exact e.symm.trans h

theorem integerJacobi_reflect (n : ℕ) :
    (integerJacobi n).comp (1-X)=C ((-1:ℤ)^n)*integerJacobi n := by
  have h := low_reflection n
  have e : (-1:ℤ[X])^n*(-1:ℤ[X])^n=1 := by
    rw [←mul_pow]
    simp
  have hh : (shiftedLegendre (n+1)).derivative.comp (1-X) =
      (-1:ℤ[X])^n*(shiftedLegendre (n+1)).derivative := by
    calc
      _ = ((-1:ℤ[X])^n*(-1:ℤ[X])^n)*((shiftedLegendre (n+1)).derivative.comp (1-X)) := by rw [e,one_mul]
      _ = _ := by rw [mul_assoc,h]
  rw [integerJacobi,mul_comp,C_comp,hh]
  simp only [map_pow,map_neg,map_one]
  ring

variable {K : Type*} [Field K] [CharZero K]

abbrev fieldJacobi (K : Type*) [Field K] (n : ℕ) : K[X] :=
  (integerJacobi n).map (Int.castRingHom K)

theorem fieldJacobi_degree (n : ℕ) : (fieldJacobi K n).natDegree=n := by
  rw [fieldJacobi,natDegree_map_eq_of_injective (Int.cast_injective (α:=K)),integerJacobi_degree]

theorem fieldJacobi_nonzero (n : ℕ) : fieldJacobi K n≠0 := by
  intro zero
  have iz := (Polynomial.map_eq_zero_iff (f:=Int.castRingHom K) Int.cast_injective).mp zero
  exact (mul_ne_zero (C_ne_zero.mpr (pow_ne_zero _ (by decide)))
    (derivative_ne_zero.mpr (by rw [natDegree_shiftedLegendre]; omega))) iz

theorem fieldJacobi_scale (n : ℕ) :
    ∃ a : K,a≠0 ∧ fieldJacobi K n=C a*jacobiTwo K n := by
  let J := (mappedLegendre K (n+1)).derivative
  let s := (-1:K)^(n+1)
  have J0 : J≠0 := jacobiTwo_raw_ne n
  have l0 : J.leadingCoeff≠0 := leadingCoeff_ne_zero.mpr J0
  refine ⟨s*J.leadingCoeff,mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) l0,?_⟩
  change (integerJacobi n).map (Int.castRingHom K)=C (s*J.leadingCoeff)*normalize J
  rw [integerJacobi,Polynomial.map_mul,Polynomial.map_C,←derivative_map,
    normalize_apply,coe_normUnit_of_ne_zero J0]
  simp only [map_pow,map_neg,map_one]
  change (-1:K[X])^(n+1)*J=C (s*J.leadingCoeff)*(J*C J.leadingCoeff⁻¹)
  rw [show (-1:K[X])^(n+1)=C s by simp [s]]
  have m : C J.leadingCoeff*C J.leadingCoeff⁻¹=1 := by
    rw [←map_mul,mul_inv_cancel₀ l0,map_one]
  rw [map_mul,show C s*C J.leadingCoeff*(J*C J.leadingCoeff⁻¹)=
    C s*J*(C J.leadingCoeff*C J.leadingCoeff⁻¹) by ring,m,mul_one]

omit [CharZero K] in
theorem fieldJacobi_reflect (n : ℕ) :
    reflectPolynomial (fieldJacobi K n)=C ((-1:K)^n)*fieldJacobi K n := by
  have h := congrArg (Polynomial.map (Int.castRingHom K)) (integerJacobi_reflect n)
  simp only [Polynomial.map_comp,Polynomial.map_sub,Polynomial.map_one,Polynomial.map_X,
    Polynomial.map_mul,map_pow,map_neg,map_one,reflectPolynomial,fieldJacobi] at h ⊢
  simpa [Polynomial.map_pow,Polynomial.map_neg] using h

omit [CharZero K] in
theorem fieldJacobi_pencil_reflect (n : ℕ) (a : K) :
    reflectPolynomial (fieldJacobi K (n+1)+C a*fieldJacobi K n) =
      C ((-1:K)^(n+1))*(fieldJacobi K (n+1)+C (-a)*fieldJacobi K n) := by
  change (fieldJacobi K (n+1)+C a*fieldJacobi K n).comp (1-X)=_
  rw [add_comp,mul_comp,C_comp]
  change reflectPolynomial (fieldJacobi K (n+1))+C a*reflectPolynomial (fieldJacobi K n)=_
  rw [fieldJacobi_reflect,fieldJacobi_reflect,pow_succ,show C (-a) = -C a from map_neg C a,
    C_mul]
  simp
  ring

theorem fieldJacobi_adjacent_coprime (n : ℕ) :
    IsCoprime (fieldJacobi K (n+1)) (fieldJacobi K n) := by
  obtain ⟨a,a0,ra⟩ := fieldJacobi_scale (K:=K) (n+1)
  obtain ⟨b,b0,rb⟩ := fieldJacobi_scale (K:=K) n
  have unit (c : K) (c0 : c≠0) (Q : K[X]) : IsCoprime (C c) Q := by
    refine ⟨C c⁻¹,0,?_⟩
    rw [zero_mul,add_zero,←map_mul,inv_mul_cancel₀ c0,map_one]
  rw [ra,rb]
  exact (unit a a0 _).mul_left ((unit b b0 _).symm.mul_right (jacobiTwo_adjacent_coprime n))

theorem fieldJacobi_omitted_low_nonzero {n : ℕ} {u a : K}
    (h : (fieldJacobi K (n+1)+C a*fieldJacobi K n).eval u=0) :
    (fieldJacobi K n).eval u≠0 := by
  intro he
  rw [eval_add,eval_mul,eval_C,he,mul_zero,add_zero] at h
  obtain ⟨P,Q,e⟩ := fieldJacobi_adjacent_coprime (K:=K) n
  have d := congrArg (eval u) e
  simp only [eval_add,eval_mul,h,he,mul_zero,zero_add,eval_one] at d
  exact zero_ne_one d

end
end RKCert.FixedPolynomial
