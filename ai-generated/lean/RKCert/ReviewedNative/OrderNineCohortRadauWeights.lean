module
public import RKCert.ReviewedNative.OrderNineCohortSupport

@[expose] public section

/-! # Native Radau and annihilator-weight normalizations -/
namespace RKResearch.Certified.Graded.MultiOff
open RKResearch Module Polynomial OneOff Reverse RKCert.Endpoint
open scoped Matrix Classical
variable {K : Type*} [Field K] [CharZero K] {s p : ℕ}

theorem order9_on_quadrature_weight_norm
    {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : (Fin (s+1)→K)} (ha : ∀i j,i≤j → A i j=0)
    (ho : HasOrder A b 9) (hM : (cleanKnots A).card=5)
    (hoff : ∀ x∈offKnots A, offMass A b x=0) :
    ∃ t : K, t≠0 ∧ ∀ x∈cleanKnots A, x≠0 →
      onWeight A b x*RKCert.Paired.nodalSlope (cleanKnots A) x*RKCert.Paired.fixedRadauT3 x=t := by
  let S := cleanKnots A
  let T := S.erase 0
  have h0 : (0:K)∈S := zero_mem_cleanKnots ha
  have hTc : T.card=4 := by
    have hCd : T.card+1=(cleanKnots A).card := Finset.card_erase_add_one h0
    omega
  let w (x : K) := onWeight A b x*x*RKCert.Paired.fixedRadauT3 x
  have hm (Q : K[X]) (hQ : Q.natDegree+2≤T.card) : ∑ x∈T,w x*Q.eval x=0 := by
    have hdd : (X*RKCert.Paired.radauCubic*Q).natDegree≤6 := by
      have hh := natDegree_mul_le_of_le (natDegree_mul_le_of_le (by simp : (X:K[X]).natDegree≤1)
        RKCert.Paired.radauCubic_degree_le) (show Q.natDegree≤2 from by omega)
      exact hh
    have hEq : probe A b 0 (evalNodes A (X*RKCert.Paired.radauCubic*Q))=0 := by
      rw [probe_evalNodes ho _ 0 (by omega),pow_zero,one_mul,←scalar_primitive]
      exact RKCert.Paired.radauCubic_weighted_primitive Q (by omega)
    rw [probe_eq_on_weights hoff] at hEq
    simp only [pow_zero,one_mul,eval_mul,eval_X,RKCert.Paired.radauCubic_eval,←mul_assoc] at hEq
    change ∑ x∈S,w x*Q.eval x=0 at hEq
    have hsum := Finset.sum_erase_add S (fun x => w x*Q.eval x) h0
    change (∑ x∈T,w x*Q.eval x)+_= (∑ x∈S,w x*Q.eval x) at hsum
    rw [hEq] at hsum
    simpa [w] using hsum
  have hex : ∃ x∈T, RKCert.Paired.fixedRadauT3 x≠0 := by
    by_contra! h
    apply RKCert.Paired.radauCubic_ne_zero (K:=K)
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ T
      (fun x hx => by rw [RKCert.Paired.radauCubic_eval,h x hx])
    have hd := RKCert.Paired.radauCubic_degree_le (K:=K)
    omega
  obtain ⟨a,haT,haNZ⟩ := hex
  obtain ⟨ha0,haS⟩ := Finset.mem_erase.mp haT
  let t := w a*RKCert.Paired.nodalSlope T a
  have ht : t≠0 := mul_ne_zero (mul_ne_zero
    (mul_ne_zero (order9_five_on_weights_nonzero ho hM hoff haS) ha0) haNZ) (RKCert.Paired.nodalSlope_ne_zero T a)
  refine ⟨t,ht,?_⟩
  intro x hx hxn
  have hw := RKCert.Paired.nodalSlope_weight_constant T w hm (Finset.mem_erase.mpr ⟨hxn,hx⟩) haT
  rw [RKCert.Paired.nodalSlope_remove_zero S h0 hxn]
  change onWeight A b x*(x*RKCert.Paired.nodalSlope T x)*RKCert.Paired.fixedRadauT3 x=t
  dsimp [w,t] at *
  linear_combination hw

omit [CharZero K] in
/-- The nonzero weighted state row killing E5 gives the same nodal
slopes at all on coordinates. Its normalization does not require
a sign assumption. -/
theorem five_on_annihilator_weight_norm
    {A : Matrix (Fin s) (Fin s) K} {w : (Fin s→K)}
    (hw : w∈annih (treeSpace A 5))
    (hM : (cleanKnots A).card=5)
    {P : K[X]} (hPd : P.natDegree≤2)
    (hP : ∀ i, OneOff.g A i≠0 → P.eval (nodes A i)=OneOff.g A i) :
    ∃ t : K, ∀ x∈cleanKnots A, onWeight A w x*P.eval x*RKCert.Paired.nodalSlope (cleanKnots A) x=t := by
  let S := cleanKnots A
  let T := offKnots A
  let f (x : K) := onWeight A w x*P.eval x
  have hf (Q : K[X]) (hd : Q.natDegree+2≤S.card) : ∑ x∈S,f x*Q.eval x=0 := by
    change Q.natDegree+2≤(cleanKnots A).card at hd
    have hQ : Q.natDegree≤3 := by omega
    have hV : diag (OneOff.g A) (evalNodes A Q)∈treeSpace A 5 := by
      have h := pairProfile_mem_E5 A (0:K[X]) Q (by simp) hQ
      have he : evalNodes A (0:K[X])=0 := by ext i; simp
      rwa [he,zero_add] at h
    have hg := mem_annih.mp hw _ hV
    rw [row_defect_to_off_weights w P Q hP] at hg
    have he := mem_annih.mp hw _ (evalNodes_mem_treeSpace A (P*Q)
      (natDegree_mul_le_of_le hPd hQ))
    rw [row_polynomial_to_weights] at he
    simp only [eval_mul] at he
    rw [hg,add_zero] at he
    simpa only [f,mul_assoc] using he
  obtain ⟨a,ha⟩ := Finset.card_pos.mp (by change 0 < (cleanKnots A).card; omega : 0 < S.card)
  exact ⟨f a*RKCert.Paired.nodalSlope S a,fun x hx => RKCert.Paired.nodalSlope_weight_constant S f hf hx ha⟩
end RKResearch.Certified.Graded.MultiOff
