module
public import RKCert.ReviewedNative.OrderNineMultiHighTerminal

@[expose] public section

/-! # Excluding all high-off order-nine candidates using the fixed scalar gates -/
namespace RKResearch.Certified.Graded.MultiOff
open RKResearch Module Polynomial OneOff RKCert.Endpoint
open scoped Matrix Classical
variable {K : Type*} [Field K] [CharZero K] {s p : ℕ}

omit [CharZero K] in
theorem beta_probe_coeff {A : Matrix (Fin s) (Fin s) K} {b : (Fin s→K)}
    (ho : HasOrder A b p) (Q : K[X]) {n k : ℕ}
    (hd : Q.natDegree ≤ n) (hpay : k+n+3 ≤ p)
    (h : probe A b k (evalNodes A ((X^2-X)*Q))=0) :
    (∑ j : Fin (n+1), Q.coeff j.val / ((k+j.val+3:ℕ):K)) -
      (∑ j : Fin (n+1), Q.coeff j.val / ((k+j.val+2:ℕ):K))=0 := by
  have he :
      probe A b k (evalNodes A ((X^2-X)*Q)) =
        probe A b (k+2) (evalNodes A Q) - probe A b (k+1) (evalNodes A Q) := by
    simp only [probe,row_apply,dotProduct,evalNodes_apply,←Finset.sum_sub_distrib,eval_mul,eval_sub,eval_pow,eval_X]
    apply Finset.sum_congr rfl
    intro i _
    simp only [pow_add,pow_one]
    ring
  rw [he,evalNodes_eq_coeffEval A Q hd,probe_coeffEval ho (by omega),
    probe_coeffEval ho (by omega)] at h
  have e (j : Fin (n+1)) : k+2+j.val+1=k+j.val+3 := by omega
  have e' (j : Fin (n+1)) : k+1+j.val+1=k+j.val+2 := by omega
  simpa only [e,e'] using h

theorem beta_cubic_from_actual_probes {A : Matrix (Fin s) (Fin s) K} {b : (Fin s→K)}
    (ho : HasOrder A b p) (hp : 8 ≤ p) (Q : K[X]) (hd : Q.natDegree ≤ 3)
    (hz : ∀ k : Fin 3, probe A b k.val (evalNodes A ((X^2-X)*Q))=0) :
    Q = C (Q.coeff 3)*RKCert.Paired.lobattoCubic := by
  apply RKCert.Paired.lobatto_cubic_decoder Q hd
  intro k
  exact beta_probe_coeff ho Q hd (by have := k.isLt; omega) (hz k)

variable [LinearOrder K] [IsStrictOrderedRing K]
omit [CharZero K] in
theorem order9_no_eight_or_more_off {A : Matrix (Fin 12) (Fin 12) K} {b : (Fin 12→K)}
    (ha : ∀i j,i≤j → A i j=0) (ho : HasOrder A b 9) :
    (offKnots A).card<8 := by
  by_contra! N
  obtain ⟨_,h3,h4,_⟩ := order9_forward_chart ha ho (by decide)
  obtain ⟨P,dP,pn,_,hF,fit⟩ := two_curve_head h3 h4 (by omega)
  obtain ⟨n,m,pdeg,notOn⟩ := order9_high_off_head_form ha ho N hF P dP pn fit
  obtain ⟨hi,hc,hu⟩ := order9_high_off_terminal ha ho m n P dP fit notOn
  obtain ⟨h,d,hn,hd,hprim,htest⟩ := order9_high_off_two_root_tests ha ho m hF P dP pn fit hi hc hu
  let a := P.leadingCoeff
  let W := C a⁻¹*P
  let H := (X-C h)*((X-C d)*W)
  have na : a≠0 := leadingCoeff_ne_zero.mpr pn
  have wM : W.Monic := by
    change (C a⁻¹*P).leadingCoeff=1
    rw [leadingCoeff_mul,leadingCoeff_C]
    exact inv_mul_cancel₀ na
  have hM : H.Monic := (monic_X_sub_C _).mul ((monic_X_sub_C _).mul wM)
  have eD : H.natDegree=2+P.natDegree := by
    change ((X-C h)*((X-C d)*W)).natDegree=2+P.natDegree
    rw [natDegree_mul (X_sub_C_ne_zero _) ((monic_X_sub_C _).mul wM).ne_zero,
      natDegree_mul (X_sub_C_ne_zero _) wM.ne_zero,natDegree_X_sub_C,natDegree_X_sub_C]
    have eW : W.natDegree=P.natDegree := natDegree_C_mul (inv_ne_zero na)
    rw [eW]
    omega
  rcases pdeg with e|e
  · have d3 : H.natDegree=3 := by omega
    have c3 : H.coeff 3=1 := by rw [←d3]; exact hM.coeff_natDegree
    have f := beta_cubic_from_actual_probes ho (by decide) H d3.le htest
    have f' : H=RKCert.Paired.lobattoCubic := by simpa [c3] using f
    exact RKCert.Paired.lobatto_cubic_complement_primitive_ne_zero e hn f'.symm ((scalar_primitive (X*P)).symm ▸ hprim)
  · have d4 : H.natDegree=4 := by omega
    have c4 : H.coeff 4=1 := by rw [←d4]; exact hM.coeff_natDegree
    have f := RKCert.Paired.beta_quartic_decoder H d4.le c4 (fun k =>
      beta_probe_coeff ho H d4.le (by have := k.isLt; omega) (htest k))
    exact RKCert.Paired.lobattoPencil_complement_primitive_ne_zero dP hn hd f.symm ((scalar_primitive (X*P)).symm ▸ hprim)

omit [CharZero K] in
/-- The only remaining ordered order-nine twelve-stage candidates have five,
six, or seven distinct defective clocks. Their separate clean supports
have five or six clocks and satisfy a common quadratic fit. -/
theorem order9_middle_census {A : Matrix (Fin 12) (Fin 12) K} {b : Fin 12→K}
    (ha : ∀i j,i≤j → A i j=0) (ho : HasOrder A b 9) :
    5≤(offKnots A).card ∧ (offKnots A).card≤7 ∧
    5≤(cleanKnots A).card ∧ (cleanKnots A).card≤6 ∧
    (offKnots A).card+(cleanKnots A).card≤12 ∧
    ∀x∈offKnots A,offMass A b x=0 := by
  have lo := order9_at_least_five_off ha ho (by decide)
  have hi := order9_no_eight_or_more_off ha ho
  obtain ⟨P,_,_,_,_,fit⟩ := order9_two_curve_head ha ho (by decide) (by omega)
  obtain ⟨cancel,clean⟩ := order9_multi_quadrature ha ho (by decide) (by omega) (by omega)
  have cle := order9_on_count_le_six ha ho (by omega) P fit cancel
  have count := clean_off_count A
  exact ⟨lo,by omega,clean,cle,by omega,cancel⟩
end RKResearch.Certified.Graded.MultiOff
