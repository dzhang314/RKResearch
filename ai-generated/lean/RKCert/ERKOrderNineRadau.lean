module

public import RKCert.ERKLowLobatto

@[expose] public section

/-! # The actual order-nine Radau profile and two fixed-root ratio gates -/
namespace RKCert.Paired
open Module Polynomial RKCert.Endpoint
open scoped Classical

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
theorem anchor_probe_coeff {A : Fin s → Fin s → K} {b : Vec K s}
    (ho : HasTreeOrderAtLeast A b p) (Q : K[X]) {n k : ℕ}
    (hd : Q.natDegree ≤ n) (hpay : k+n+2 ≤ p)
    (hz : probe A b k (evalNodes A (X*Q))=0) :
    (∑ j : Fin (n+1), Q.coeff j.val / ((k+j.val+2:ℕ):K))=0 := by
  have he : probe A b k (evalNodes A (X*Q)) = probe A b (k+1) (evalNodes A Q) := by
    simp only [probe,row_apply,evalNodes_apply,eval_mul,eval_X,pow_succ]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he,evalNodes_eq_polyEval A Q hd,probe_polyEval ho (by omega)] at hz
  have e (j : Fin (n+1)) : k+1+j.val+1=k+j.val+2 := by omega
  simpa only [e] using hz

/-- Exact p9 moment consequences: all roots of the monic hull of the
nonzero on nodes satisfy the fixed Radau quartic. -/
theorem order9_nodal_radau {A : Fin (s+1) → Fin (s+1) → K} {b : Vec K (s+1)}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 9)
    (hM : (onNodes A).card=5)
    (hoff : ∀ x∈supportedNodes A (qdef A), offWeight A b x=0) :
    nodalHull ((onNodes A).erase 0)=radauQuartic := by
  let S := (onNodes A).erase 0
  let Q := nodalHull S
  have h0 := zero_mem_onNodes ha
  have hS : S.card+1=(onNodes A).card := Finset.card_erase_add_one h0
  have hd : Q.natDegree=4 := by
    change (nodalHull S).natDegree=4
    rw [natDegree_nodalHull]; omega
  have he := radau_quartic_decoder Q hd.le (fun i => by
    apply anchor_probe_coeff ho Q hd.le (by have := i.isLt; omega)
    rw [← show nodalHull (onNodes A)=X*Q by
      rw [nodalHull_erase_factor _ h0,map_zero,sub_zero]]
    exact probes_zero_of_on_roots hoff _ (fun _ => nodalHull_eval_of_mem) i.val)
  have hc : Q.coeff 4=1 := hd ▸ (monic_nodalHull S).coeff_natDegree
  simpa [hc] using he

omit [CharZero K] in
theorem radau_on_root {A : Fin s → Fin s → K}
    (hQ : nodalHull ((onNodes A).erase 0)=radauQuartic) {x : K}
    (hOn : x∈onNodes A) (hx : x≠0) : radauQuartic.eval x=0 := by
  rw [←hQ]
  exact nodalHull_eval_of_mem (Finset.mem_erase.mpr ⟨hx,hOn⟩)

set_option maxHeartbeats 900000 in
/-- The necessary first/second chronological on-node ratio in the rank-nine
branch is impossible over every characteristic-zero field. -/
theorem radau_ratio_three_fourths (x : K) (h1 : radauQuartic.eval x=0)
    (h2 : radauQuartic.eval (3*x/4)=0) : False := by
  simp [radauQuartic] at h1 h2
  have hf : 126*x^4-280*x^3+210*x^2-60*x+5=0 := by linear_combination 126*h1
  have hg : 5103*x^4-15120*x^3+15120*x^2-5760*x+640=0 := by linear_combination 16128*h2
  have hz : (98101775:K)=0 := by
    linear_combination (-1037215368*x^3+826022610*x^2+897617700*x-368110845)*hf +
      (25610256*x^3-1425060*x^2-14260680*x+3029150)*hg
  exact (by norm_num : (98101775:K)≠0) hz

set_option maxHeartbeats 900000 in
theorem radau_ratio_half (x : K) (h1 : radauQuartic.eval x=0)
    (h2 : radauQuartic.eval (x/2)=0) : False := by
  simp [radauQuartic] at h1 h2
  have hf : 126*x^4-280*x^3+210*x^2-60*x+5=0 := by linear_combination 126*h1
  have hg : 63*x^4-280*x^3+420*x^2-240*x+40=0 := by linear_combination 1008*h2
  have hz : (5675:K)=0 := by
    linear_combination (-28728*x^3+99330*x^2-90540*x+10175)*hf +
      (57456*x^3-70980*x^2+19800*x-1130)*hg
  exact (by norm_num : (5675:K)≠0) hz

end RKCert.Paired

