module
public import RKCert.ReviewedNative.OrderNineSixOnPrefix

@[expose] public section

/-! # Nonzero native beta quadrature and its state-row normalizers -/
namespace RKResearch.Certified.Graded.MultiOff
open RKResearch Module Polynomial OneOff Reverse RKCert.Endpoint
open scoped Matrix Classical
variable {K : Type*} [Field K] [CharZero K] {s p : ℕ}

/-- The exact weighted moment functional supplies a nonzero common
normalization on all four ordinary on nodes. No positivity is assumed;
the fixed cubic square is evaluated as a nonzero rational. -/
theorem order9_six_on_weight_norm {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : (Fin (s+1)→K)}
    (ha : ∀i j,i≤j → A i j=0) (ho : HasOrder 9 A b)
    (hM : (cleanKnots A).card=6) (one : (1:K)∈cleanKnots A)
    (off : ∀x∈offKnots A,offMass A b x=0) :
    ∃ t : K,t≠0 ∧ ∀x∈RKCert.Paired.endpointErase (cleanKnots A) 1,x≠0 →
      onWeight A b x*(1-x)*RKCert.Paired.nodalSlope (RKCert.Paired.endpointErase (cleanKnots A) 1) x*RKCert.Paired.lobattoCubic.eval x=t := by
  let S := RKCert.Paired.endpointErase (cleanKnots A) 1
  let T := RKCert.Paired.endpointErase S 0
  have hz : (0:K)∈S := Finset.mem_erase.mpr ⟨zero_ne_one,zero_mem_cleanKnots ha⟩
  have hs : S.card+1=(cleanKnots A).card := Finset.card_erase_add_one one
  have ht : T.card+1=S.card := Finset.card_erase_add_one hz
  have t4 : T.card=4 := by omega
  let w (x : K) := onWeight A b x*x*(1-x)*RKCert.Paired.lobattoCubic.eval x
  have mom (Q : K[X]) (dQ : Q.natDegree≤3) :
      (∑x∈T,w x*Q.eval x)=(primitive ((X-X^2)*RKCert.Paired.lobattoCubic*Q)).eval 1 := by
    have dx1 : (X : K[X]).natDegree≤2 := by simp
    have dx2 : (X^2 : K[X]).natDegree≤2 := by simp
    have dx : (X-X^2 : K[X]).natDegree≤2 := natDegree_sub_le_of_le dx1 dx2
    have dg : ((X-X^2)*RKCert.Paired.lobattoCubic*Q).natDegree≤8 :=
      natDegree_mul_le_of_le (natDegree_mul_le_of_le dx RKCert.Paired.lobattoCubic_degree.le) dQ
    have e := probe_evalNodes ho ((X-X^2)*RKCert.Paired.lobattoCubic*Q) 0 (by omega)
    rw [pow_zero,one_mul,probe_eq_on_weights off] at e
    simp only [pow_zero,one_mul,eval_mul,eval_sub,eval_X,eval_pow] at e
    have e' (x : K) : onWeight A b x * ((x-x^2)*RKCert.Paired.lobattoCubic.eval x*Q.eval x)=
        w x*Q.eval x := by dsimp [w]; ring
    rw [Finset.sum_congr rfl (fun x _ => e' x)] at e
    have st := Finset.sum_erase_add (cleanKnots A) (fun x => w x*Q.eval x) one
    have sr := Finset.sum_erase_add S (fun x => w x*Q.eval x) hz
    change (∑x∈S,w x*Q.eval x)+w 1*Q.eval 1=(∑x∈cleanKnots A,w x*Q.eval x) at st
    change (∑x∈T,w x*Q.eval x)+w 0*Q.eval 0=(∑x∈S,w x*Q.eval x) at sr
    rw [←st,←sr] at e
    simpa [w] using e
  have tm (Q : K[X]) (dQ : Q.natDegree+2≤T.card) : ∑x∈T,w x*Q.eval x=0 := by
    rw [mom Q (by omega),←scalar_primitive ((X-X^2)*RKCert.Paired.lobattoCubic*Q)]
    exact RKCert.Paired.beta_lobattoCubic_pair Q (by omega)
  obtain ⟨a,haT,ha0⟩ : ∃a∈T,w a≠0 := by
    by_contra! none
    have eg := mom (RKCert.Paired.lobattoCubic : K[X]) RKCert.Paired.lobattoCubic_degree.le
    have z : (∑x∈T,w x*RKCert.Paired.lobattoCubic.eval x)=0 :=
      Finset.sum_eq_zero (fun x hx => by simp [none x hx])
    rw [z,←scalar_primitive,RKCert.Paired.beta_lobattoCubic_square] at eg
    exact (by norm_num : (1/35280:K)≠0) eg.symm
  refine ⟨w a*RKCert.Paired.nodalSlope T a,mul_ne_zero ha0 (RKCert.Paired.nodalSlope_ne_zero T a),?_⟩
  intro x hx hn
  have en := RKCert.Paired.nodalSlope_weight_constant T w tm (Finset.mem_erase.mpr ⟨hn,hx⟩) haT
  have eS : RKCert.Paired.nodalSlope S x=x*RKCert.Paired.nodalSlope T x := RKCert.Paired.nodalSlope_remove_zero S hz hn
  change onWeight A b x*(1-x)*RKCert.Paired.nodalSlope S x*RKCert.Paired.lobattoCubic.eval x=_
  rw [eS]
  dsimp [w] at en ⊢
  linear_combination en

omit [CharZero K] in
/-- The actual annihilating row has the complementary nodal slope
normalization on the nonterminal clean nodes. -/
theorem five_six_annihilator_weight_norm {A : Matrix (Fin s) (Fin s) K} {w : (Fin s→K)}
    (hw : w∈annih (treeSpace A 5)) (hM : (cleanKnots A).card=6)
    {P : K[X]} (dP : P.natDegree≤2)
    (fit : ∀ i,g A i≠0 → P.eval (nodes A i)=g A i)
    (one : (1:K)∈cleanKnots A) (wend : onWeight A w 1=0) :
    ∃ t : K, ∀x∈RKCert.Paired.endpointErase (cleanKnots A) 1,
      onWeight A w x*P.eval x*RKCert.Paired.nodalSlope (RKCert.Paired.endpointErase (cleanKnots A) 1) x=t := by
  let S := RKCert.Paired.endpointErase (cleanKnots A) 1
  let f (x : K) := onWeight A w x*P.eval x
  have dS : S.card+1=(cleanKnots A).card := Finset.card_erase_add_one one
  have hf (Q : K[X]) (hd : Q.natDegree+2≤S.card) : ∑x∈S,f x*Q.eval x=0 := by
    have hQ : Q.natDegree≤3 := by omega
    have qg : diag (g A) (evalNodes A Q)∈treeSpace A 5 := by
      have h := pairProfile_mem_E5 A (0:K[X]) Q (by simp) hQ
      have he : evalNodes A (0:K[X])=0 := by ext i; simp
      rwa [he,zero_add] at h
    have hg := mem_annih.mp hw _ qg
    rw [row_defect_to_off_weights w P Q fit] at hg
    have e := mem_annih.mp hw _ (evalNodes_mem_treeSpace A (P*Q) (natDegree_mul_le_of_le dP hQ))
    rw [row_polynomial_to_weights] at e
    simp only [eval_mul] at e
    rw [hg,add_zero] at e
    have es : (∑x∈cleanKnots A,f x*Q.eval x)=0 := by simpa only [f,mul_assoc] using e
    have re := Finset.sum_erase_add (cleanKnots A) (fun x => f x*Q.eval x) one
    change (∑x∈S,f x*Q.eval x)+_=(∑x∈cleanKnots A,f x*Q.eval x) at re
    rw [es] at re
    simpa [f,wend] using re
  obtain ⟨a,ha⟩ := Finset.card_pos.mp (show 0<S.card by omega)
  exact ⟨f a*RKCert.Paired.nodalSlope S a,fun x hx => RKCert.Paired.nodalSlope_weight_constant S f hf hx ha⟩
end RKResearch.Certified.Graded.MultiOff
