module

public import RKCert.ERKOrderNineFiveSixPrefix

@[expose] public section

/-! # Nonzero exact beta quadrature and the ordinary on weight slopes -/
namespace RKCert.Paired
open Module Polynomial RKCert.Endpoint
open scoped Classical

variable {K : Type*} [Field K] [CharZero K] {s : ℕ}

theorem beta_lobattoCubic_pair (Q : K[X]) (dQ : Q.natDegree≤2) :
    (primitive ((X-X^2)*lobattoCubic*Q)).eval 1=0 := by
  conv_lhs => rw [quadratic_coeff_expand Q dQ]
  simp only [lobattoCubic,sub_mul,add_mul,mul_add,X_mul_monomial,X_pow_mul_monomial,
    monomial_mul_monomial,map_add,map_sub,eval_add,eval_sub,primitive_monomial,
    eval_monomial,one_pow,mul_one,Nat.reduceAdd,Nat.cast_ofNat]
  ring

theorem beta_lobattoCubic_square :
    (primitive ((X-X^2)*lobattoCubic*lobattoCubic : K[X])).eval 1=1/35280 := by
  simp only [lobattoCubic,sub_mul,add_mul,mul_add,X_mul_monomial,X_pow_mul_monomial,
    monomial_mul_monomial,map_add,map_sub,eval_add,eval_sub,primitive_monomial,
    eval_monomial,one_pow,mul_one,Nat.reduceAdd,Nat.cast_ofNat]
  norm_num

/-- The exact weighted moment functional supplies a nonzero common
normalization on all four ordinary on nodes. No positivity is assumed;
the fixed cubic square is evaluated as a nonzero rational. -/
theorem order9_six_on_weight_norm {A : Fin (s+1)→Fin (s+1)→K} {b : Vec K (s+1)}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 9)
    (hM : (onNodes A).card=6) (one : (1:K)∈onNodes A)
    (off : ∀x∈supportedNodes A (qdef A),offWeight A b x=0) :
    ∃ t : K,t≠0 ∧ ∀x∈endpointErase (onNodes A) 1,x≠0 →
      onWeight A b x*(1-x)*nodalSlope (endpointErase (onNodes A) 1) x*lobattoCubic.eval x=t := by
  let S := endpointErase (onNodes A) 1
  let T := endpointErase S 0
  have hz : (0:K)∈S := Finset.mem_erase.mpr ⟨zero_ne_one,zero_mem_onNodes ha⟩
  have hs : S.card+1=(onNodes A).card := Finset.card_erase_add_one one
  have ht : T.card+1=S.card := Finset.card_erase_add_one hz
  have t4 : T.card=4 := by omega
  let w (x : K) := onWeight A b x*x*(1-x)*lobattoCubic.eval x
  have mom (Q : K[X]) (dQ : Q.natDegree≤3) :
      (∑x∈T,w x*Q.eval x)=(primitive ((X-X^2)*lobattoCubic*Q)).eval 1 := by
    have dx1 : (X : K[X]).natDegree≤2 := by simp
    have dx2 : (X^2 : K[X]).natDegree≤2 := by simp
    have dx : (X-X^2 : K[X]).natDegree≤2 := natDegree_sub_le_of_le dx1 dx2
    have dg : ((X-X^2)*lobattoCubic*Q).natDegree≤8 :=
      natDegree_mul_le_of_le (natDegree_mul_le_of_le dx lobattoCubic_degree.le) dQ
    have e := row_polynomial_eq_unit_primitive ho _ dg (by decide)
    have p : row b (evalNodes A ((X-X^2)*lobattoCubic*Q))=
        probe A b 0 (evalNodes A ((X-X^2)*lobattoCubic*Q)) := by simp [probe]
    rw [p,probe_eq_on_weights off] at e
    simp only [pow_zero,one_mul,eval_mul,eval_sub,eval_X,eval_pow] at e
    have e' (x : K) : onWeight A b x * ((x-x^2)*lobattoCubic.eval x*Q.eval x)=
        w x*Q.eval x := by dsimp [w]; ring
    rw [Finset.sum_congr rfl (fun x _ => e' x)] at e
    have st := Finset.sum_erase_add (onNodes A) (fun x => w x*Q.eval x) one
    have sr := Finset.sum_erase_add S (fun x => w x*Q.eval x) hz
    change (∑x∈S,w x*Q.eval x)+w 1*Q.eval 1=(∑x∈onNodes A,w x*Q.eval x) at st
    change (∑x∈T,w x*Q.eval x)+w 0*Q.eval 0=(∑x∈S,w x*Q.eval x) at sr
    rw [←st,←sr] at e
    simpa [w] using e
  have tm (Q : K[X]) (dQ : Q.natDegree+2≤T.card) : ∑x∈T,w x*Q.eval x=0 :=
    (mom Q (by omega)).trans (beta_lobattoCubic_pair Q (by omega))
  obtain ⟨a,haT,ha0⟩ : ∃a∈T,w a≠0 := by
    by_contra! none
    have eg := mom (lobattoCubic : K[X]) lobattoCubic_degree.le
    have z : (∑x∈T,w x*lobattoCubic.eval x)=0 :=
      Finset.sum_eq_zero (fun x hx => by simp [none x hx])
    rw [z,beta_lobattoCubic_square] at eg
    exact (by norm_num : (1/35280:K)≠0) eg.symm
  refine ⟨w a*nodalSlope T a,mul_ne_zero ha0 (nodalSlope_ne_zero T a),?_⟩
  intro x hx hn
  have en := nodalSlope_weight_constant T w tm (Finset.mem_erase.mpr ⟨hn,hx⟩) haT
  have eS : nodalSlope S x=x*nodalSlope T x := nodalSlope_remove_zero S hz hn
  change onWeight A b x*(1-x)*nodalSlope S x*lobattoCubic.eval x=_
  rw [eS]
  dsimp [w] at en ⊢
  linear_combination en

/-- The actual annihilating row has the complementary nodal slope
normalization on the nonterminal clean nodes. -/
theorem five_six_annihilator_weight_norm {A : Fin s→Fin s→K} {w : Vec K s}
    (hw : w∈annih (treeSpace A 5)) (hM : (onNodes A).card=6)
    {P : K[X]} (dP : P.natDegree≤2)
    (fit : ∀ i,qdef A i≠0 → P.eval (nodes A i)=qdef A i)
    (one : (1:K)∈onNodes A) (wend : onWeight A w 1=0) :
    ∃ t : K, ∀x∈endpointErase (onNodes A) 1,
      onWeight A w x*P.eval x*nodalSlope (endpointErase (onNodes A) 1) x=t := by
  let S := endpointErase (onNodes A) 1
  let f (x : K) := onWeight A w x*P.eval x
  have dS : S.card+1=(onNodes A).card := Finset.card_erase_add_one one
  have hf (Q : K[X]) (hd : Q.natDegree+2≤S.card) : ∑x∈S,f x*Q.eval x=0 := by
    have hQ : Q.natDegree≤3 := by omega
    have qg : diag (qdef A) (evalNodes A Q)∈treeSpace A 5 := by
      have h := pairProfile_mem_E5 A (0:K[X]) Q (by simp) hQ
      have he : evalNodes A (0:K[X])=0 := by ext i; simp
      rwa [he,zero_add] at h
    have hg := mem_annih.mp hw _ qg
    rw [row_defect_to_off_weights w P Q fit] at hg
    have e := mem_annih.mp hw _ (evalNodes_mem_treeSpace A (P*Q) (natDegree_mul_le_of_le dP hQ))
    rw [row_polynomial_to_weights] at e
    simp only [eval_mul] at e
    rw [hg,add_zero] at e
    have es : (∑x∈onNodes A,f x*Q.eval x)=0 := by simpa only [f,mul_assoc] using e
    have re := Finset.sum_erase_add (onNodes A) (fun x => f x*Q.eval x) one
    change (∑x∈S,f x*Q.eval x)+_=(∑x∈onNodes A,f x*Q.eval x) at re
    rw [es] at re
    simpa [f,wend] using re
  obtain ⟨a,ha⟩ := Finset.card_pos.mp (show 0<S.card by omega)
  exact ⟨f a*nodalSlope S a,fun x hx => nodalSlope_weight_constant S f hf hx ha⟩

end RKCert.Paired
