module
public import RKCert.FourDebutBarycentric
@[expose] public section
namespace RKCert.FourDebut
open RKCert.Paired Module Polynomial
variable {K : Type*} [Field K] [CharZero K]

noncomputable def Z2 (a b : K) : Polynomial K := (X-C a)*(X-C b)
noncomputable def Z3 (a b u : K) : Polynomial K := (X-C a)*(X-C b)*(X-C u)
omit [CharZero K] in
private theorem Jterm (a : K) (n : ℕ) :
    primitive (C a*X^n) = C (a/((n+1:ℕ):K))*X^(n+1) := by
  rw [C_mul_X_pow_eq_monomial,primitive_monomial,C_mul_X_pow_eq_monomial]

theorem primitive2 (a b x : K) :
    (primitive (X*Z2 a b)).eval x=x^2*L2 a b x := by
  have e : X*Z2 a b = C 1*X^3-C (a+b)*X^2+C (a*b)*X^1 := by
    simp only [Z2,map_one,map_add,map_mul]; ring
  rw [e,map_add,map_sub,Jterm,Jterm,Jterm]
  simp only [eval_add,eval_sub,eval_mul,eval_pow,eval_X,eval_C,L2]; norm_num; ring

theorem primitive31 (a b u x : K) :
    (primitive (X*Z3 a b u)).eval x=B1 a b u x := by
  have e : X*Z3 a b u=C 1*X^4-C (a+b+u)*X^3+C (a*b+u*(a+b))*X^2-C (a*b*u)*X^1 := by
    simp only [Z3,map_one,map_add,map_mul]; ring
  rw [e,map_sub,map_add,map_sub,Jterm,Jterm,Jterm,Jterm]
  simp only [eval_add,eval_sub,eval_mul,eval_pow,eval_X,eval_C,B1]; norm_num; ring

theorem primitive32 (a b u x : K) :
    (primitive (X^2*Z3 a b u)).eval x=B2 a b u x := by
  have e : X^2*Z3 a b u=C 1*X^5-C (a+b+u)*X^4+C (a*b+u*(a+b))*X^3-C (a*b*u)*X^2 := by
    simp only [Z3,map_one,map_add,map_mul]; ring
  rw [e,map_sub,map_add,map_sub,Jterm,Jterm,Jterm,Jterm]
  simp only [eval_add,eval_sub,eval_mul,eval_pow,eval_X,eval_C,B2]; norm_num; ring

omit [CharZero K] in
theorem represent0 {Q : Polynomial K} (q : Q.degree<(1:WithBot ℕ)) (x : K) : Q.eval x=Q.coeff 0 := by
  by_cases h:Q=0
  · simp [h]
  · have d : Q.natDegree<1 := (Polynomial.natDegree_lt_iff_degree_lt h).mpr q
    calc
      Q.eval x = (C (Q.coeff 0)).eval x := congrArg (fun P : Polynomial K => P.eval x) (Polynomial.eq_C_of_natDegree_eq_zero (by omega))
      _ = Q.coeff 0 := eval_C

omit [CharZero K] in
theorem represent1 {Q : Polynomial K} (q : Q.degree<(2:WithBot ℕ)) (x : K) :
    Q.eval x=Q.coeff 1*x+Q.coeff 0 := by
  by_cases h:Q=0
  · simp [h]
  · have d := (Polynomial.natDegree_lt_iff_degree_lt h).mpr q
    rw [Polynomial.eval_eq_sum_range' d]
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_one,pow_zero,mul_one]
    ring

omit [CharZero K] in
theorem represent2 {Q : Polynomial K} (q : Q.degree<(3:WithBot ℕ)) (x : K) :
    Q.eval x=Q.coeff 2*x^2+Q.coeff 1*x+Q.coeff 0 := by
  by_cases h:Q=0
  · simp [h]
  · have d := (Polynomial.natDegree_lt_iff_degree_lt h).mpr q
    rw [Polynomial.eval_eq_sum_range' d]
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_one,pow_zero,mul_one]
    ring
end RKCert.FourDebut
