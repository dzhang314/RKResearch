module

public import RKCert.ERKLowFourOff

@[expose] public section

/-! # Exact endpoint primitive and beta-moment tests for the low-order cases -/
namespace RKCert.Paired
open Module Polynomial
open scoped Classical

variable {K : Type*} [Field K] [CharZero K] {s p : ℕ}

theorem on_primitive_exact {A : Fin s → Fin s → K} {i : Fin s}
    (hF : zeroSpace A 4 = chainSpan A (qdef A) 2) (hi : qdef A i = 0)
    (Q : K[X]) (hq : Q.natDegree ≤ 3) :
    mat A (evalNodes A Q) i = (primitive Q).eval (nodes A i) := by
  have hz := primitive_defect A Q hq
  rw [hF,chainSpan_iff_polynomial] at hz
  obtain ⟨P,_,hP⟩ := hz
  have hh := congrFun hP i
  exact sub_eq_zero.mp (by simpa [hi] using hh)

theorem on_primitive_zero_of_prefix {A : Fin s → Fin s → K} {i : Fin s}
    (ha : StrictLower A) (hF : zeroSpace A 4 = chainSpan A (qdef A) 2)
    (hi : qdef A i = 0) (Q : K[X]) (hq : Q.natDegree ≤ 3)
    (v : Vec K s) (hv : mat A v i = 0)
    (hpre : ∀ j, j < i → Q.eval (nodes A j) = v j) :
    (primitive Q).eval (nodes A i) = 0 := by
  have hz := causal_mat ha i (evalNodes A Q-v) (fun j hj => sub_eq_zero.mpr (hpre j hj))
  rw [map_sub,Pi.sub_apply,hv,sub_zero,on_primitive_exact hF hi Q hq] at hz
  exact hz

omit [CharZero K] in
theorem quadratic_coeff_expand (P : K[X]) (hp : P.natDegree ≤ 2) :
    P = monomial 0 (P.coeff 0) + monomial 1 (P.coeff 1) + monomial 2 (P.coeff 2) := by
  nth_rw 1 [P.as_sum_range' 3 (by omega)]
  simp [Finset.sum_range_succ]

omit [CharZero K] in
theorem primitive_eval_quadratic (P : K[X]) (hp : P.natDegree ≤ 2) (u : K) :
    (primitive P).eval u = P.coeff 0*u + P.coeff 1*u^2/2 + P.coeff 2*u^3/3 := by
  conv_lhs => rw [quadratic_coeff_expand P hp]
  simp only [map_add,primitive_monomial,eval_add,eval_monomial,Nat.reduceAdd,Nat.cast_one,
    div_one,pow_one,Nat.cast_ofNat,div_mul_eq_mul_div]

omit [CharZero K] in
theorem primitive_eval_X_quadratic (P : K[X]) (hp : P.natDegree ≤ 2) (u : K) :
    (primitive (X*P)).eval u = P.coeff 0*u^2/2 + P.coeff 1*u^3/3 + P.coeff 2*u^4/4 := by
  conv_lhs => rw [quadratic_coeff_expand P hp]
  simp only [mul_add,X_mul_monomial,map_add,primitive_monomial,eval_add,eval_monomial,
    Nat.reduceAdd,Nat.cast_ofNat,div_mul_eq_mul_div]

theorem first_nonzero_on_forces_head_shape {A : Fin s → Fin s → K}
    (ha : StrictLower A) (hF : zeroSpace A 4 = chainSpan A (qdef A) 2)
    {P : K[X]} (hd : P.natDegree ≤ 2) (hn : P ≠ 0)
    (hP : ∀ j, qdef A j ≠ 0 → P.eval (nodes A j) = qdef A j)
    (hex : ∃ i, qdef A i = 0 ∧ nodes A i ≠ 0) :
    P.eval 0 ≠ 0 ∧ 1 ≤ P.natDegree := by
  let U : Set (Fin s) := {i | qdef A i = 0 ∧ nodes A i ≠ 0}
  have hU : U.Nonempty := hex
  obtain ⟨i,hi,hmin⟩ := wellFounded_lt.has_min U hU
  rcases (show qdef A i=0 ∧ nodes A i≠0 from hi) with ⟨hdi,hni⟩
  let u := nodes A i
  change u ≠ 0 at hni
  have hzero (j : Fin s) (hj : j < i) (hj' : qdef A j=0) : nodes A j=0 := by
    by_contra h
    exact hmin j ⟨hj',h⟩ hj
  obtain ⟨_,hA,hAC⟩ := on_row_quartic_conditions hF hdi
  have hXd : (X*P).natDegree ≤ 3 := Polynomial.natDegree_mul_le_of_le (by simp) hd
  have hxP := on_primitive_zero_of_prefix ha hF hdi (X*P) hXd
    (diag (nodes A) (qdef A)) hAC (fun j hj => by
      by_cases hg : qdef A j=0
      · simp [hg,hzero j hj hg]
      · simp [hP j hg])
  rw [primitive_eval_X_quadratic P hd] at hxP
  change P.coeff 0*u^2/2 + P.coeff 1*u^3/3 + P.coeff 2*u^4/4 = 0 at hxP
  constructor
  · intro h
    have hz : P.coeff 0=0 := (coeff_zero_eq_eval_zero P).trans h
    have hP' := on_primitive_zero_of_prefix ha hF hdi P (by omega) (qdef A) hA
      (fun j hj => by
        by_cases hg : qdef A j=0
        · rw [hzero j hj hg,h,hg]
        · exact hP j hg)
    rw [primitive_eval_quadratic P hd] at hP'
    change P.coeff 0*u + P.coeff 1*u^2/2 + P.coeff 2*u^3/3 = 0 at hP'
    have hb : P.coeff 2 * u^4=0 := by linear_combination 36*hxP - 24*u*hP' + 6*u^2*hz
    have hb' := (mul_eq_zero.mp hb).resolve_right (pow_ne_zero _ hni)
    rw [hz,hb'] at hP'
    have h : P.coeff 1*u^2=0 := by linear_combination 2*hP'
    have ha' := (mul_eq_zero.mp h).resolve_right (pow_ne_zero _ hni)
    apply hn
    rw [quadratic_coeff_expand P hd,hz,ha',hb']
    simp
  · by_contra! h
    have hC : P = C (P.coeff 0) := eq_C_of_natDegree_eq_zero (by omega)
    have h1 : P.coeff 1=0 := by nth_rw 1 [hC]; simp
    have h2 : P.coeff 2=0 := by nth_rw 1 [hC]; simp
    rw [h1,h2] at hxP
    have h0 : P.coeff 0*u^2=0 := by linear_combination 2*hxP
    have hp0 := (mul_eq_zero.mp h0).resolve_right (pow_ne_zero _ hni)
    exact hn (by rw [hC,hp0,map_zero])

omit [CharZero K] in
theorem exists_nonzero_on_of_card {A : Fin s → Fin s → K}
    (h : 2 ≤ (onNodes A).card) : ∃ i, qdef A i=0 ∧ nodes A i≠0 := by
  by_contra! h'
  have hs : onNodes A ⊆ ({0}:Finset K) := by
    intro x hx
    obtain ⟨i,hi,rfl⟩ := mem_onNodes.mp hx
    simpa using h' i hi
  have hn := Finset.card_le_card hs
  simp at hn
  omega

omit [CharZero K] in
/-- Convert the genuine `X(X-1)` probe into the two shifted sums, with
the exact tree-order budget visible in the statement. -/
theorem beta_probe_coeff {A : Fin s → Fin s → K} {b : Vec K s}
    (ho : HasTreeOrderAtLeast A b p) (Q : K[X]) {n k : ℕ}
    (hd : Q.natDegree ≤ n) (hpay : k+n+3 ≤ p)
    (h : probe A b k (evalNodes A ((X^2-X)*Q))=0) :
    (∑ j : Fin (n+1), Q.coeff j.val / ((k+j.val+3:ℕ):K)) -
      (∑ j : Fin (n+1), Q.coeff j.val / ((k+j.val+2:ℕ):K))=0 := by
  have he :
      probe A b k (evalNodes A ((X^2-X)*Q)) =
        probe A b (k+2) (evalNodes A Q) - probe A b (k+1) (evalNodes A Q) := by
    simp only [probe,row_apply,evalNodes_apply,←Finset.sum_sub_distrib,eval_mul,eval_sub,eval_pow,eval_X]
    apply Finset.sum_congr rfl
    intro i _
    simp only [pow_add,pow_one]
    ring
  rw [he,evalNodes_eq_polyEval A Q hd,probe_polyEval ho (by omega),
    probe_polyEval ho (by omega)] at h
  have e (j : Fin (n+1)) : k+2+j.val+1=k+j.val+3 := by omega
  have e' (j : Fin (n+1)) : k+1+j.val+1=k+j.val+2 := by omega
  simpa only [e,e'] using h

noncomputable def lobattoCubic : K[X] :=
  monomial 0 (-1/14) + monomial 1 (9/14) + monomial 2 (-3/2) + monomial 3 1

set_option maxHeartbeats 600000 in
theorem lobatto_cubic_decoder (Q : K[X]) (hd : Q.natDegree ≤ 3)
    (hm : ∀ i : Fin 3,
      (∑ j : Fin 4, Q.coeff j.val / ((i.val+j.val+3:ℕ):K)) -
      (∑ j : Fin 4, Q.coeff j.val / ((i.val+j.val+2:ℕ):K))=0) :
    Q = C (Q.coeff 3) * lobattoCubic := by
  have h0 := hm 0
  have h1 := hm 1
  have h2 := hm 2
  norm_num [Fin.sum_univ_succ] at h0 h1 h2
  have hQ0 : Q.coeff 0 = Q.coeff 3*(-1/14) := by linear_combination -120*h0 + 480*h1 - 420*h2
  have hQ1 : Q.coeff 1 = Q.coeff 3*(9/14) := by linear_combination 480*h0 - 2220*h1 + 2100*h2
  have hQ2 : Q.coeff 2 = Q.coeff 3*(-3/2) := by linear_combination -420*h0 + 2100*h1 - 2100*h2
  ext n
  by_cases h : n≤3
  · interval_cases n <;> simp [coeff_C_mul,lobattoCubic,coeff_monomial,hQ0,hQ1,hQ2]
  · rw [coeff_eq_zero_of_natDegree_lt (by omega : Q.natDegree < n),coeff_C_mul]
    simp only [lobattoCubic,coeff_add,coeff_monomial]
    have h0' : 0≠n := by omega
    have h1' : 1≠n := by omega
    have h2' : 2≠n := by omega
    have h3' : 3≠n := by omega
    simp [h0',h1',h2',h3']

omit [CharZero K] in
theorem lobatto_isRoot_of_linear {P : K[X]} {u : K}
    (h : lobattoCubic = (X-C u)*P) : lobattoCubic.eval u=0 := by rw [h]; simp

set_option maxHeartbeats 400000 in
/-- The first physical clean node is excluded when its omitted
quadratic factor is the other two roots of the order-eight Lobatto cubic. -/
theorem lobatto_first_on_scalar_gate {P : K[X]} (hP : P.natDegree≤2)
    {u : K} (hu : u≠0) (h : lobattoCubic = (X-C u)*P)
    (hprim : (primitive (X*P)).eval u=0) : False := by
  have h0 := lobatto_isRoot_of_linear h
  have hr : 14*u^3 - 21*u^2 + 9*u - 1 = 0 := by
    simp [lobattoCubic] at h0
    linear_combination 14*h0
  have hcoef (n : ℕ) : (lobattoCubic : K[X]).coeff (n+1) =
      P.coeff n - u*P.coeff (n+1) := by
    rw [h,sub_mul,coeff_sub,coeff_X_mul,coeff_C_mul]
  have h3 := hcoef 2
  have h2 := hcoef 1
  have h1 := hcoef 0
  have hz : P.coeff 3=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  norm_num [lobattoCubic,coeff_monomial,hz] at h3 h2 h1
  rw [primitive_eval_X_quadratic P hP] at hprim
  have hq : u^2 * (91*u^2 - 105*u + 27)=0 := by
    linear_combination 84*hprim + 91*u^4*h3 + 70*u^3*h2 + 42*u^2*h1
  have hg := (mul_eq_zero.mp hq).resolve_left (pow_ne_zero _ hu)
  have hbad : (1:K)=0 := by
    linear_combination (232/11-819*u/22)*hr + (63*u^2/11-115*u/22+9/11)*hg
  exact one_ne_zero hbad

end RKCert.Paired

