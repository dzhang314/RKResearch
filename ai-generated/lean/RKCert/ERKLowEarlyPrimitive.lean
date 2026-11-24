module

public import RKCert.ERKOrderNineFiveSixPrefix

@[expose] public section

/-! # Primitive tests on a grade-three/null prefix

These are algebraic and apply to the actual chronological tableau.
The primitive of the polynomial component is separated before
restricting to earlier rows. No quadrature positivity is used.
-/
namespace RKCert.Paired
open Polynomial RKCert.Endpoint
open scoped Classical
variable {K : Type*} [Field K] [CharZero K] {s : ℕ}

theorem degree_three_actual_mat_profile {A : Fin s→Fin s→K}
    (hF : zeroSpace A 4=chainSpan A (qdef A) 2)
    (Q R : K[X]) (dQ : Q.natDegree≤3) (dR : R.natDegree≤1) :
    ∃ J : K[X], J.natDegree≤2 ∧
      mat A (evalNodes A Q+diag (qdef A) (evalNodes A R))=
        evalNodes A (primitive Q)+diag (qdef A) (evalNodes A J) := by
  have hr : diag (qdef A) (evalNodes A R)∈zeroSpace A 3 :=
    chainSpan_le_zeroSpace (qdef_mem A) 1 (chainSpan_iff_polynomial.mpr ⟨R,dR,rfl⟩)
  have hQ := primitive_defect A Q dQ
  have hv := (zeroSpace A 4).add_mem hQ (mat_zeroSpace_charZero A 3 hr)
  rw [hF,chainSpan_iff_polynomial] at hv
  obtain ⟨J,hJ,eJ⟩ := hv
  refine ⟨J,hJ,?_⟩
  rw [map_add,←eJ]
  abel

omit [CharZero K] in
theorem cubic_coeff_expand (P : K[X]) (dP : P.natDegree≤3) :
    P=monomial 0 (P.coeff 0)+monomial 1 (P.coeff 1)+monomial 2 (P.coeff 2)+monomial 3 (P.coeff 3) := by
  nth_rw 1 [P.as_sum_range' 4 (by omega)]
  simp [Finset.sum_range_succ]

omit [CharZero K] in
theorem primitive_eval_cubic (P : K[X]) (dP : P.natDegree≤3) (x : K) :
    (primitive P).eval x=P.coeff 0*x+P.coeff 1*x^2/2+P.coeff 2*x^3/3+P.coeff 3*x^4/4 := by
  conv_lhs => rw [cubic_coeff_expand P dP]
  simp only [map_add,primitive_monomial,eval_add,eval_monomial,Nat.reduceAdd,Nat.cast_one,
    div_one,pow_one,Nat.cast_ofNat,div_mul_eq_mul_div]

/-- The unique nonzero cubic axis with zeros at zero and h and with a
zero primitive at h has its exact double-square primitive. -/
theorem cubic_zero_at_origin_and_node_primitive
    (P : K[X]) (dP : P.natDegree≤3) (pn : P≠0) {h : K}
    (hn : h≠0) (h0 : P.eval 0=0) (hh : P.eval h=0) (hp : (primitive P).eval h=0) :
    ∃ a : K,a≠0 ∧ primitive P=C a*(X^2*(X-C h)^2) := by
  have hd0 : P.coeff 0=0 := (coeff_zero_eq_eval_zero P).trans h0
  have he (x : K) : P.eval x=P.coeff 1*x+P.coeff 2*x^2+P.coeff 3*x^3 := by
    conv_lhs => rw [cubic_coeff_expand P dP]
    simp [hd0]
  rw [he] at hh
  rw [primitive_eval_cubic P dP,hd0,zero_mul,zero_add] at hp
  have e2 : P.coeff 2= -(3/2)*h*P.coeff 3 := by
    apply mul_left_cancel₀ (pow_ne_zero 3 hn)
    linear_combination 3*h*hh-6*hp
  have e1 : P.coeff 1=(h^2/2)*P.coeff 3 := by
    apply mul_left_cancel₀ hn
    linear_combination hh-h^2*e2
  have n3 : P.coeff 3≠0 := by
    intro e
    apply pn
    rw [cubic_coeff_expand P dP,hd0,e1,e2,e]
    simp
  refine ⟨P.coeff 3/4,div_ne_zero n3 (by norm_num),?_⟩
  let _ : Infinite K := Infinite.of_injective (fun n : ℕ => (n:K)) Nat.cast_injective
  apply Polynomial.funext
  intro x
  rw [primitive_eval_cubic P dP,hd0,e1,e2]
  simp
  ring

/-- A nonzero constant coefficient prevents a quadratic head dividing
its own x-weighted primitive. This eliminates a hidden zero-residual
case in both early-prefix placements. -/
theorem quadratic_head_not_dvd_own_weighted_primitive {P : K[X]}
    (dP : P.natDegree=2) (h0 : P.eval 0≠0) : ¬P∣primitive (X*P) := by
  intro div
  have n0 : P.coeff 0≠0 := fun h => h0 ((coeff_zero_eq_eval_zero P).symm.trans h)
  have pn : P≠0 := fun h => n0 (by simp [h])
  have n2 : P.coeff 2≠0 := by
    rw [←dP,←leadingCoeff]
    exact leadingCoeff_ne_zero.mpr pn
  let T : K[X] := monomial 0 (P.coeff 0/2)+monomial 1 (P.coeff 1/3)+monomial 2 (P.coeff 2/4)
  have eq : primitive (X*P)=X^2*T := by
    let _ : Infinite K := Infinite.of_injective (fun n : ℕ => (n:K)) Nat.cast_injective
    apply Polynomial.funext
    intro x
    rw [primitive_eval_X_quadratic P dP.le]
    simp [T]
    ring
  have tp : IsCoprime P (X:K[X]) :=
    (irreducible_X.coprime_iff_not_dvd.mpr (fun e=>n0 (X_dvd_iff.mp e))).symm
  rw [eq] at div
  obtain ⟨U,he⟩ := (tp.pow_right (n:=2)).dvd_of_dvd_mul_left div
  have t0 : T.coeff 0=P.coeff 0/2 := by simp [T]
  have t2 : T.coeff 2=P.coeff 2/4 := by simp [T,coeff_monomial]
  have tn : T≠0 := by intro e; rw [e,coeff_zero] at t2; exact (div_ne_zero n2 (by norm_num)) t2.symm
  have tu : U≠0 := fun e => tn (by simp [he,e])
  have dr : T.natDegree≤2 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    have e0 : 0≠i := by omega
    have e1 : 1≠i := by omega
    have e2 : 2≠i := by omega
    simp [T,coeff_monomial,coeff_C,Ne.symm e0,e1,e2]
  have du : U.natDegree=0 := by
    have hd := natDegree_mul pn tu
    rw [←he,dP] at hd
    omega
  have hu := eq_C_of_natDegree_eq_zero du
  let a := U.coeff 0
  have te : T=C a*P := by rw [he,hu]; exact mul_comm _ _
  have h0' : a*P.coeff 0=P.coeff 0/2 := by rw [te,coeff_C_mul] at t0; exact t0
  have h2' : a*P.coeff 2=P.coeff 2/4 := by rw [te,coeff_C_mul] at t2; exact t2
  have ar : a=(1/2:K) := by
    apply mul_right_cancel₀ n0
    linear_combination h0'
  have ar' : a=(1/4:K) := by
    apply mul_right_cancel₀ n2
    linear_combination h2'
  have e := ar.symm.trans ar'
  norm_num at e

end RKCert.Paired
