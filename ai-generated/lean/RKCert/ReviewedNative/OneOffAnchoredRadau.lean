module

public import RKCert.ReviewedNative.OneOffCleanClocks
public import Mathlib.Tactic.IntervalCases

@[expose] public section

/-! # Exact anchored-polynomial kernel and the paid terminal coordinate -/
namespace RKResearch.Certified.Graded.OneOff
open RKResearch Polynomial Module
open scoped Classical Matrix

variable {K : Type*} [Field K] [CharZero K] {s p : ℕ}

noncomputable def radauQuartic : K[X] :=
  monomial 0 (5/126) + monomial 1 (-10/21) + monomial 2 (5/3) +
    monomial 3 (-20/9) + monomial 4 1

set_option maxHeartbeats 900000 in
theorem radau_quartic_decoder (Q : K[X]) (hd : Q.natDegree ≤ 4)
    (hm : ∀ i : Fin 4, (∑ j : Fin 5, Q.coeff j.val / ((i.val+j.val+2:ℕ):K))=0) :
    Q = C (Q.coeff 4)*radauQuartic := by
  have h0 := hm 0
  have h1 := hm 1
  have h2 := hm 2
  have h3 := hm 3
  norm_num [Fin.sum_univ_succ] at h0 h1 h2 h3
  have c0 : Q.coeff 0=Q.coeff 4*(5/126) := by
    linear_combination 200*h0 - 1200*h1 + 2100*h2 - 1120*h3
  have c1 : Q.coeff 1=Q.coeff 4*(-10/21) := by
    linear_combination -1200*h0 + 8100*h1 - 15120*h2 + 8400*h3
  have c2 : Q.coeff 2=Q.coeff 4*(5/3) := by
    linear_combination 2100*h0 - 15120*h1 + 29400*h2 - 16800*h3
  have c3 : Q.coeff 3=Q.coeff 4*(-20/9) := by
    linear_combination -1120*h0 + 8400*h1 - 16800*h2 + 9800*h3
  ext n
  by_cases h : n≤4
  · interval_cases n <;> simp [coeff_C_mul,radauQuartic,c0,c1,c2,c3]
  · rw [coeff_eq_zero_of_natDegree_lt (by omega : Q.natDegree < n),coeff_C_mul]
    simp only [radauQuartic,coeff_add,coeff_monomial]
    have h0' : 0≠n := by omega
    have h1' : 1≠n := by omega
    have h2' : 2≠n := by omega
    have h3' : 3≠n := by omega
    have h4' : 4≠n := by omega
    simp [h0',h1',h2',h3',h4']

omit [CharZero K] in
theorem anchor_probe_coeff {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
    (ho : HasOrder p A b) (Q : K[X]) {n k : ℕ}
    (hd : Q.natDegree ≤ n) (hpay : k+n+2 ≤ p)
    (hz : probe A b k (evalNodes A (X*Q))=0) :
    (∑ j : Fin (n+1), Q.coeff j.val / ((k+j.val+2:ℕ):K))=0 := by
  have he : probe A b k (evalNodes A (X*Q)) = probe A b (k+1) (evalNodes A Q) := by
    simp only [probe,row_apply,dotProduct,evalNodes_apply,eval_mul,eval_X,pow_succ]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he,evalNodes_eq_coeffEval A Q hd,probe_coeffEval ho (by omega)] at hz
  have e (j : Fin (n+1)) : k+1+j.val+1=k+j.val+2 := by omega
  simpa only [e] using hz

noncomputable def anchorRadau : K[X] := X*radauQuartic

theorem anchorRadau_at_one : (anchorRadau : K[X]).eval 1=1/126 := by
  norm_num [anchorRadau,radauQuartic]

omit [CharZero K] in
theorem anchorRadau_coeff_five : (anchorRadau : K[X]).coeff 5=1 := by
  rw [anchorRadau,coeff_X_mul]
  simp [radauQuartic,coeff_monomial]

/-- Any degree-five polynomial part in a grade-five relation at p9
belongs to this one-dimensional span, with its own top coefficient. -/
theorem anchored_radau_span {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
    (ho : HasOrder 9 A b) (P : K[X]) (dp : P.natDegree≤5)
    (p0 : P.eval 0=0)
    (mom : ∀ j : Fin 4, probe A b j.val (evalNodes A P)=0) :
    P=C (P.coeff 5)*anchorRadau := by
  have hC : P.coeff 0=0 := by rwa [coeff_zero_eq_eval_zero]
  obtain ⟨Q,e⟩ := X_dvd_iff.mpr hC
  have dq : Q.natDegree≤4 := by
    by_cases n : Q=0
    · simp [n]
    · have h := natDegree_mul X_ne_zero n
      rw [←e,natDegree_X] at h
      omega
  have dec := radau_quartic_decoder Q dq (fun j =>
    anchor_probe_coeff ho Q dq (by have := j.isLt; omega) (e ▸ mom j))
  have cf : P.coeff 5=Q.coeff 4 := by rw [e,coeff_X_mul]
  calc
    P=X*Q := e
    _=X*(C (Q.coeff 4)*radauQuartic) := congrArg (X * ·) dec
    _=C (P.coeff 5)*anchorRadau := by rw [cf,anchorRadau]; ring

end RKResearch.Certified.Graded.OneOff
