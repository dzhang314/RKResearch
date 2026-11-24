module

public import RKCert.ERKOrderNineSixSix

@[expose] public section

/-! # High-off head reduction without ordered quadrature

Cauchy moment injectivity handles the short moment systems in place of
positive integrals. Only the later free-pencil endpoint needs an order
on the coefficient field.
-/
namespace RKCert.Paired
open Module Polynomial RKCert.Endpoint RKCert.FixedFactor
open scoped Classical

variable {K : Type*} [Field K] [CharZero K] {s p : ℕ}

theorem probe_head_product_zero {A : Fin s → Fin s → K} {b : Vec K s}
    (ho : HasTreeOrderAtLeast A b p) {P : K[X]}
    (fit : ∀ i, qdef A i≠0 → P.eval (nodes A i)=qdef A i)
    (Q : K[X]) (on : ∀ x∈onNodes A,P.eval x*Q.eval x=0)
    (k : ℕ) (pay : k+Q.natDegree+3≤p) :
    probe A b k (evalNodes A (P*Q))=0 := by
  have he : evalNodes A (P*Q)=diag (evalNodes A Q) (qdef A) := by
    ext i
    by_cases h : qdef A i=0
    · have h' := on _ (mem_onNodes.mpr ⟨i,h,rfl⟩)
      simpa [h,eval_mul] using h'
    · simp [eval_mul,fit i h,mul_comm]
  rw [he]
  have hz : signal A (qdef A) k∈zeroSpace A (2+k) :=
    chainSpan_le_zeroSpace (qdef_mem A) k (signal_mem_chainSpan A _ le_rfl)
  have hp' : probe A b k (diag (evalNodes A Q) (qdef A)) =
      row b (diag (evalNodes A Q) (signal A (qdef A) k)) := by
    simp only [probe,row_apply,diag_apply,signal]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hp']
  exact defect_polynomial_pair_zero ho (by omega) hz Q le_rfl

omit [CharZero K] in
theorem anchored_poly_zero_of_probes {A : Fin s → Fin s → K} {b : Vec K s}
    (ho : HasTreeOrderAtLeast A b p) (n : ℕ) (pay : 2*n+2≤p)
    (Q : K[X]) (hd : Q.natDegree≤n)
    (hm : ∀ k : Fin (n+1), probe A b k.val (evalNodes A (X*Q))=0) : Q=0 := by
  let a : Fin (n+1) → K := fun j => Q.coeff j.val
  have hs (k : Fin (n+1)) : (∑ j : Fin (n+1),a j/((k.val+j.val+2:ℕ):K))=0 :=
    anchor_probe_coeff ho Q hd (by have := k.isLt; omega) (hm k)
  have hz := moments_detect ho (d:=2) (by decide) (by omega) (fun i j => by omega) a hs
  ext k
  by_cases hk : k<n+1
  · exact hz ⟨k,hk⟩
  · simpa using (coeff_eq_zero_of_natDegree_lt (by omega : Q.natDegree<k))

theorem order9_head_not_constant {A : Fin s → Fin s → K} {b : Vec K s}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 9)
    (hF : zeroSpace A 4=chainSpan A (qdef A) 2)
    (P : K[X]) (dp : P.natDegree≤2) (pn : P≠0)
    (fit : ∀ i,qdef A i≠0 → P.eval (nodes A i)=qdef A i) : 1≤P.natDegree := by
  by_cases ex : ∃ i, qdef A i=0 ∧ nodes A i≠0
  · exact (first_nonzero_on_forces_head_shape ha hF dp pn fit ex).2
  · by_contra! h
    have hC : P=C (P.coeff 0) := eq_C_of_natDegree_eq_zero (by omega)
    have hz := probe_head_product_zero ho fit X (fun x hx => by
      obtain ⟨i,hi,rfl⟩ := mem_onNodes.mp hx
      have hc : nodes A i=0 := by by_contra hn; exact ex ⟨i,hi,hn⟩
      simp [hc]) 0 (by simp)
    have hq := anchored_poly_zero_of_probes ho 0 (by decide) P (by omega) (by
      intro k
      fin_cases k
      simpa [mul_comm] using hz)
    exact pn hq

/-- Every high-off candidate is actually an eight-off/four-on chart
whose head has degree one or two and never vanishes on a clean node. -/
theorem order9_high_off_head_form {A : Fin 12 → Fin 12 → K} {b : Vec K 12}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 9)
    (hN : 8≤(supportedNodes A (qdef A)).card)
    (hF : zeroSpace A 4=chainSpan A (qdef A) 2)
    (P : K[X]) (dp : P.natDegree≤2) (pn : P≠0)
    (fit : ∀ i,qdef A i≠0 → P.eval (nodes A i)=qdef A i) :
    (supportedNodes A (qdef A)).card=8 ∧ (onNodes A).card=4 ∧
      (P.natDegree=1 ∨ P.natDegree=2) ∧ ∀ x∈onNodes A,P.eval x≠0 := by
  have cap := on_off_card_le A
  have hM : (onNodes A).card≤4 := by omega
  have dp0 := order9_head_not_constant ha ho hF P dp pn fit
  let T := (onNodes A).filter (fun x => P.eval x≠0)
  let Q := nodalHull T
  let G := P*Q
  have dQ : Q.natDegree=T.card := natDegree_nodalHull _
  have qn : Q≠0 := (monic_nodalHull _).ne_zero
  have gn : G≠0 := mul_ne_zero pn qn
  have dG : G.natDegree=P.natDegree+T.card := by simp only [G,natDegree_mul pn qn,dQ]
  have leT : T.card≤(onNodes A).card := Finset.card_filter_le _ _
  have on (x : K) (hx : x∈onNodes A) : P.eval x*Q.eval x=0 := by
    by_cases hp : P.eval x=0
    · rw [hp,zero_mul]
    · rw [show Q.eval x=0 from nodalHull_eval_of_mem (Finset.mem_filter.mpr ⟨hx,hp⟩),mul_zero]
  have gm (k : ℕ) (hk : k+T.card+3≤9) : probe A b k (evalNodes A G)=0 :=
    probe_head_product_zero ho fit Q on k (by rwa [dQ])
  have zeroG : G.eval 0=0 := by simp only [G,eval_mul]; exact on 0 (zero_mem_onNodes ha)
  obtain ⟨W,ew⟩ := X_dvd_iff.mpr ((coeff_zero_eq_eval_zero G).trans zeroG)
  have wn : W≠0 := fun e => gn (by simp [ew,e])
  have dw : G.natDegree=1+W.natDegree := by rw [ew,natDegree_mul X_ne_zero wn,natDegree_X]
  have dGmin : 5≤G.natDegree := by
    by_contra! lt
    by_cases d1 : P.natDegree=1
    · apply wn
      apply anchored_poly_zero_of_probes ho W.natDegree (by omega) W le_rfl
      intro k
      have hk := k.isLt
      rw [←ew]
      exact gm _ (by omega)
    · have d2 : P.natDegree=2 := by omega
      apply gn
      apply zero_of_full_profile_probes ho G.natDegree (by omega) G le_rfl
      intro k
      have hk := k.isLt
      exact gm _ (by omega)
  have d2not5 : P.natDegree=2 → G.natDegree≠5 := by
    intro d2 dg5
    have dW : W.natDegree=4 := by omega
    have wr := radau_quartic_decoder W dW.le (fun k => by
      have hk := k.isLt
      apply anchor_probe_coeff ho W dW.le (by omega)
      rw [←ew]
      exact gm _ (by omega))
    let a := W.coeff 4
    have an : a≠0 := by
      change W.coeff 4≠0
      rw [←dW,←leadingCoeff]
      exact leadingCoeff_ne_zero.mpr wn
    have eg : G=C a*(X*radauQuartic) := by rw [ew,wr]; ring
    have hdv : P∣X*radauQuartic := ⟨C a⁻¹*Q,by
      calc X*radauQuartic=C a⁻¹*G := by rw [eg,←mul_assoc,←map_mul,inv_mul_cancel₀ an,map_one,one_mul]
      _=P*(C a⁻¹*Q) := by dsimp only [G]; ring⟩
    obtain ⟨h,hh,hn,test⟩ := first_nonzero_clean_test ha hF P dp fit
      (exists_nonzero_on_of_card (by omega))
    have hz : G.eval h=0 := by simp only [G,eval_mul]; exact on h hh
    have hroot : radauQuartic.eval h=0 := by
      rw [eg,eval_mul,eval_C,eval_mul,eval_X] at hz
      exact (mul_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left an)).resolve_left hn
    exact radau_divisor_first_moment hdv dp hn hroot test
  have T4 : T.card=4 := by
    by_cases d1 : P.natDegree=1
    · omega
    · have d2 : P.natDegree=2 := by omega
      have lg : 6≤G.natDegree := by have := d2not5 d2; omega
      omega
  have eqT : T=onNodes A := Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
  refine ⟨by omega,by omega,by omega,?_⟩
  intro x hx
  have hx' : x∈T := eqT.symm ▸ hx
  exact (Finset.mem_filter.mp hx').2

end RKCert.Paired
