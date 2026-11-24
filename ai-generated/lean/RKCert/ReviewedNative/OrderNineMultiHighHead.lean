module
public import RKCert.ReviewedNative.OrderNineMultiLow
public import RKCert.ReviewedNative.OrderNineMultiScalar

@[expose] public section

/-! # The only high-off chart is exactly eight off and four clean -/
namespace RKResearch.Certified.Graded.MultiOff
open RKResearch Module Polynomial OneOff RKCert.Endpoint
open scoped Matrix Classical
variable {K : Type*} [Field K] [CharZero K] {s p : ℕ}

omit [CharZero K] in
/-- Product of the two head curves vanishes at every affordable probe
whenever its value vanishes on the clean knots. -/
theorem probe_head_product_zero {A : Matrix (Fin s) (Fin s) K} {b : Fin s→K}
    (ho : HasOrder p A b) {P : K[X]} (fit : ∀i,g A i≠0 → P.eval (nodes A i)=g A i)
    (Q : K[X]) (on : ∀ x∈cleanKnots A, P.eval x*Q.eval x=0)
    (k : ℕ) (pay : k+Q.natDegree+3≤p) : probe A b k (evalNodes A (P*Q))=0 := by
  apply probe_zeroSpace ho (j:=2+Q.natDegree) (by omega)
  apply band_le A Q.natDegree
  apply band_iff.mpr ⟨Q,le_rfl,?_⟩
  ext i
  by_cases hi : g A i=0
  · have z := on _ (mem_cleanKnots.mpr ⟨i,hi,rfl⟩)
    simp [hi,z]
  · simp [fit i hi]

theorem on_primitive_zero_of_prefix {A : Matrix (Fin s) (Fin s) K} {i : Fin s}
    (ha : ∀i j,i≤j → A i j=0) (hF : zeroSpace A 4=band A 2) (hi : g A i=0)
    (Q : K[X]) (hq : Q.natDegree≤3) (v : Fin s→K) (hv : mat A v i=0)
    (hpre : ∀ j, j < i → Q.eval (nodes A j)=v j) : (primitive Q).eval (nodes A i)=0 := by
  have rem := clean_four_vanish hF hi (primitive_defect A Q (q:=3) hq)
  have eq := causal_action_eq ha i (evalNodes A Q) v hpre
  change mat A (evalNodes A Q) i - (primitive Q).eval (nodes A i)=0 at rem
  rw [eq,hv,zero_sub,neg_eq_zero] at rem
  exact rem

theorem clean_mixed_defect {A : Matrix (Fin s) (Fin s) K}
    (hF : zeroSpace A 4=band A 2) {i : Fin s} (hi : g A i=0) :
    mat A (diag (nodes A) (g A)) i=0 :=
  clean_four_vanish hF hi (mat_zeroSpace_charZero A 3 (diag_zeroSpace A 2 (mDef_mem A 1)))

theorem first_nonzero_clean_test {s:ℕ} {A : Matrix (Fin s) (Fin s) K}
    (ha : ∀i j,i≤j → A i j=0) (hF : zeroSpace A 4=band A 2)
    (P : K[X]) (hd : P.natDegree≤2)
    (off : ∀i, g A i≠0 → P.eval (nodes A i)=g A i)
    (hex : ∃i, g A i=0 ∧ nodes A i≠0) :
    ∃u∈cleanKnots A, u≠0 ∧ (primitive (X*P)).eval u=0 := by
  let U : Set (Fin s) := {i | g A i=0 ∧ nodes A i≠0}
  obtain ⟨i,hi,hmin⟩ := wellFounded_lt.has_min U (show U.Nonempty from hex)
  obtain ⟨di,ni⟩ := (show g A i=0 ∧ nodes A i≠0 from hi)
  refine ⟨nodes A i,mem_cleanKnots.mpr ⟨i,di,rfl⟩,ni,?_⟩
  apply on_primitive_zero_of_prefix ha hF di (X*P) (natDegree_mul_le_of_le (by simp) hd)
    (diag (nodes A) (g A)) (clean_mixed_defect hF di)
  intro j hj
  by_cases dj : g A j=0
  · have nj : nodes A j=0 := by by_contra ne; exact hmin j ⟨dj,ne⟩ hj
    simp [nj,dj]
  · simp [off j dj]

omit [CharZero K] in
theorem exists_nonzero_on_of_card {A : Matrix (Fin s) (Fin s) K}
    (h : 2 ≤ (cleanKnots A).card) : ∃ i, g A i=0 ∧ nodes A i≠0 := by
  by_contra! h'
  have hs : cleanKnots A ⊆ ({0}:Finset K) := by
    intro x hx
    obtain ⟨i,hi,rfl⟩ := mem_cleanKnots.mp hx
    simpa using h' i hi
  have hn := Finset.card_le_card hs
  simp at hn
  omega

omit [CharZero K] in
theorem anchor_probe_coeff {A : Matrix (Fin s) (Fin s) K} {b : (Fin s→K)}
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

omit [CharZero K] in
theorem anchored_poly_zero_of_probes {A : Matrix (Fin s) (Fin s) K} {b : (Fin s→K)}
    (ho : HasOrder p A b) (n : ℕ) (pay : 2*n+2≤p)
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

theorem positive_head_degree {A : Matrix (Fin s) (Fin s) K}
    (ha : ∀i j,i≤j → A i j=0) (hF : zeroSpace A 4=band A 2)
    (P : K[X]) (hd : P.natDegree≤2) (pn : P≠0)
    (fit : ∀i,g A i≠0 → P.eval (nodes A i)=g A i)
    (ex : ∃ i, g A i=0 ∧ nodes A i≠0) : 1≤P.natDegree := by
  by_contra! lt
  have eq := eq_C_of_natDegree_eq_zero (p:=P) (by omega)
  have cn : P.coeff 0≠0 := fun h=>pn (by rw [eq,h,map_zero])
  obtain ⟨u,_,nu,j⟩ := first_nonzero_clean_test ha hF P hd fit ex
  have mon : X*P = monomial 1 (P.coeff 0) := by
    conv_lhs => rw [eq]
    rw [←C_mul_X_pow_eq_monomial,pow_one,mul_comm]
  rw [mon,primitive_monomial,eval_monomial] at j
  exact (mul_ne_zero (div_ne_zero cn (by norm_num)) (pow_ne_zero _ nu)) j

theorem order9_high_off_head_form {A : Matrix (Fin 12) (Fin 12) K} {b : (Fin 12→K)}
    (ha : ∀i j,i≤j → A i j=0) (ho : HasOrder 9 A b)
    (hN : 8≤(offKnots A).card)
    (hF : zeroSpace A 4=band A 2)
    (P : K[X]) (dp : P.natDegree≤2) (pn : P≠0)
    (fit : ∀ i,g A i≠0 → P.eval (nodes A i)=g A i) :
    (offKnots A).card=8 ∧ (cleanKnots A).card=4 ∧
      (P.natDegree=1 ∨ P.natDegree=2) ∧ ∀ x∈cleanKnots A,P.eval x≠0 := by
  have cap := clean_off_count A
  have hM : (cleanKnots A).card≤4 := by omega
  let T := (cleanKnots A).filter (fun x => P.eval x≠0)
  let Q := nodalHull T
  let G := P*Q
  have dQ : Q.natDegree=T.card := natDegree_nodalHull _
  have qn : Q≠0 := (monic_nodalHull _).ne_zero
  have gn : G≠0 := mul_ne_zero pn qn
  have dG : G.natDegree=P.natDegree+T.card := by simp only [G,natDegree_mul pn qn,dQ]
  have leT : T.card≤(cleanKnots A).card := Finset.card_filter_le _ _
  have on (x : K) (hx : x∈cleanKnots A) : P.eval x*Q.eval x=0 := by
    by_cases hp : P.eval x=0
    · rw [hp,zero_mul]
    · rw [show Q.eval x=0 from nodalHull_eval_of_mem (Finset.mem_filter.mpr ⟨hx,hp⟩),mul_zero]
  have gm (k : ℕ) (hk : k+T.card+3≤9) : probe A b k (evalNodes A G)=0 :=
    probe_head_product_zero ho fit Q on k (by rwa [dQ])
  have zeroG : G.eval 0=0 := by simp only [G,eval_mul]; exact on 0 (zero_mem_cleanKnots ha)
  obtain ⟨W,ew⟩ := X_dvd_iff.mpr ((coeff_zero_eq_eval_zero G).trans zeroG)
  have wn : W≠0 := fun e => gn (by simp [ew,e])
  have dw : G.natDegree=1+W.natDegree := by rw [ew,natDegree_mul X_ne_zero wn,natDegree_X]
  have short : T.card≤3 → 5≤G.natDegree := by
    intro small
    by_contra! lt
    apply wn
    apply anchored_poly_zero_of_probes ho W.natDegree (by omega) W le_rfl
    intro k
    have hk := k.isLt
    rw [←ew]
    exact gm _ (by omega)
  have d2not5 : P.natDegree=2 → G.natDegree≠5 := by
    intro d2 dg5
    have dW : W.natDegree=4 := by omega
    have wr := RKCert.Paired.radau_quartic_decoder W dW.le (fun k => by
      have hk := k.isLt
      apply anchor_probe_coeff ho W dW.le (by omega)
      rw [←ew]
      exact gm _ (by omega))
    let a := W.coeff 4
    have an : a≠0 := by
      change W.coeff 4≠0
      rw [←dW,←leadingCoeff]
      exact leadingCoeff_ne_zero.mpr wn
    have eg : G=C a*(X*RKCert.Paired.radauQuartic) := by rw [ew,wr]; ring
    have hdv : P∣X*RKCert.Paired.radauQuartic := ⟨C a⁻¹*Q,by
      calc X*RKCert.Paired.radauQuartic=C a⁻¹*G := by rw [eg,←mul_assoc,←map_mul,inv_mul_cancel₀ an,map_one,one_mul]
      _=P*(C a⁻¹*Q) := by dsimp only [G]; ring⟩
    obtain ⟨h,hh,hn,test⟩ := first_nonzero_clean_test ha hF P dp fit
      (exists_nonzero_on_of_card (by omega))
    have hz : G.eval h=0 := by simp only [G,eval_mul]; exact on h hh
    have hroot : RKCert.Paired.radauQuartic.eval h=0 := by
      rw [eg,eval_mul,eval_C,eval_mul,eval_X] at hz
      exact (mul_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left an)).resolve_left hn
    exact RKCert.FixedFactor.radau_divisor_first_moment hdv dp hn hroot ((scalar_primitive (X*P)).symm ▸ test)
  have T4 : T.card=4 := by
    by_contra ne
    have small : T.card≤3 := by omega
    have lo := short small
    have dp2 : P.natDegree=2 := by omega
    exact d2not5 dp2 (by omega)
  have dp0 := positive_head_degree ha hF P dp pn fit (exists_nonzero_on_of_card (by omega))
  have eqT : T=cleanKnots A := Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
  refine ⟨by omega,by omega,by omega,?_⟩
  intro x hx
  have hx' : x∈T := eqT.symm ▸ hx
  exact (Finset.mem_filter.mp hx').2
end RKResearch.Certified.Graded.MultiOff
