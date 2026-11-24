module

public import RKCert.ERKOrderNineStateSupport
public import RKCert.ERKOrderNineLateScalarBridge

@[expose] public section

/-! # Exact on-weight normalizations for both late rows -/
namespace RKCert.Paired
open Module Polynomial RKCert.Endpoint
open scoped Classical

variable {K : Type*} [Field K] {s p : ℕ}

noncomputable def nodalSlope (S : Finset K) (x : K) : K :=
  (nodalHull (S.erase x)).eval x

/-- The one-dimensional interpolation annihilator has constant
weight times nodal slope.  The proof uses a two-node polynomial
test rather than invoking partial fractions or distinctness between
two different feature sets. -/
theorem nodalSlope_weight_constant (S : Finset K) (w : K→K)
    (hm : ∀ P : K[X], P.natDegree+2 ≤ S.card → ∑ x∈S,w x*P.eval x=0)
    {a b : K} (ha : a∈S) (hb : b∈S) :
    w a*nodalSlope S a=w b*nodalSlope S b := by
  by_cases hab : a=b
  · rw [hab]
  let T := (S.erase a).erase b
  let Q := nodalHull T
  have hb' : b∈ S.erase a := Finset.mem_erase.mpr ⟨Ne.symm hab,hb⟩
  have ha' : a∈ S.erase b := Finset.mem_erase.mpr ⟨hab,ha⟩
  have hC1 := Finset.card_erase_add_one ha
  have hC2 : T.card+1=(S.erase a).card := Finset.card_erase_add_one hb'
  have hd : Q.natDegree+2≤S.card := by
    rw [show Q.natDegree=T.card from natDegree_nodalHull _]
    omega
  have he := hm Q hd
  have h1 := Finset.sum_erase_add S (fun x => w x*Q.eval x) ha
  have h2 := Finset.sum_erase_add (S.erase a) (fun x => w x*Q.eval x) hb'
  have h0 : ∑ x∈T,w x*Q.eval x=0 :=
    Finset.sum_eq_zero fun x hx => by rw [nodalHull_eval_of_mem hx,mul_zero]
  rw [←h1,←h2,h0,zero_add] at he
  have hA : nodalSlope S a=(a-b)*Q.eval a := by
    unfold nodalSlope
    rw [nodalHull_erase_factor _ hb',eval_mul,eval_sub,eval_X,eval_C]
  have hB : nodalSlope S b=(b-a)*Q.eval b := by
    unfold nodalSlope
    have hs : (S.erase b).erase a=T := by
      ext x; simp [T,Finset.mem_erase,and_left_comm]
    rw [nodalHull_erase_factor _ ha',hs,eval_mul,eval_sub,eval_X,eval_C]
  rw [hA,hB]
  linear_combination (a-b)*he

theorem nodalSlope_ne_zero (S : Finset K) (x : K) :
    nodalSlope S x≠0 := nodalHull_eval_ne_zero_of_notMem (Finset.notMem_erase _ _)

theorem nodalSlope_remove_zero (S : Finset K) (h0 : (0:K)∈S) {x : K} (hx : x≠0) :
    nodalSlope S x=x*nodalSlope (S.erase 0) x := by
  have h01 : (0:K)∈ S.erase x := Finset.mem_erase.mpr ⟨Ne.symm hx,h0⟩
  unfold nodalSlope
  have hs : (S.erase x).erase 0=(S.erase 0).erase x := by
    ext y; simp [Finset.mem_erase,and_left_comm]
  rw [nodalHull_erase_factor _ h01,hs,eval_mul,eval_sub,eval_X,eval_C,sub_zero]

variable [CharZero K]

omit [CharZero K] in
/-- Ordinary moment at one from actual bush-tree tests. -/
theorem row_polynomial_eq_unit_primitive {A : Fin s → Fin s → K} {b : Vec K s}
    (ho : HasTreeOrderAtLeast A b p) (P : K[X]) {n : ℕ} (hd : P.natDegree≤n) (hp : n+1≤p) :
    row b (evalNodes A P)=(primitive P).eval 1 := by
  have hP : (primitive P).eval 1 =
      ∑ j : Fin (n+1), P.coeff j.val / ((j.val+1:ℕ):K) := by
    conv_lhs => rw [P.as_sum_range' (n+1) (by omega)]
    simp [map_sum,primitive_monomial,Finset.sum_range,eval_finsetSum]
  rw [hP]
  have h : row b (evalNodes A P)=probe A b 0 (evalNodes A P) := by simp [probe]
  rw [h,evalNodes_eq_polyEval A P hd,probe_polyEval ho (by omega)]
  simp only [zero_add]

noncomputable def radauCubic : K[X] :=
  monomial 0 (-4/35) + monomial 1 (6/7) + monomial 2 (-12/7) + monomial 3 1

theorem radauCubic_eval (x : K) : radauCubic.eval x=fixedRadauT3 x := by
  simp [radauCubic,fixedRadauT3]
  ring

omit [CharZero K] in
theorem radauCubic_degree_le : (radauCubic : K[X]).natDegree≤3 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  have h0 : 0≠i := by omega
  have h1 : 1≠i := by omega
  have h2 : 2≠i := by omega
  have h3 : 3≠i := by omega
  simp [radauCubic,coeff_monomial,coeff_C,Ne.symm h0,h1,h2,h3]

theorem radauCubic_ne_zero : (radauCubic : K[X])≠0 := by
  intro h
  have he := congrArg (fun P : K[X] => P.coeff 3) h
  norm_num [radauCubic] at he

/-- Orthogonality of the cubic against the first three monomials,
verified directly with the pinned algebraic primitive. -/
theorem radauCubic_weighted_primitive (P : K[X]) (hp : P.natDegree≤2) :
    (primitive (X*radauCubic*P)).eval 1=0 := by
  conv_lhs => rw [quadratic_coeff_expand P hp]
  simp only [radauCubic,mul_add,add_mul,X_mul_monomial,monomial_mul_monomial,
    map_add,eval_add,primitive_monomial,eval_monomial,one_pow,mul_one,Nat.reduceAdd,Nat.cast_ofNat]
  ring

theorem order9_on_quadrature_weight_norm
    {A : Fin (s+1) → Fin (s+1) → K} {b : Vec K (s+1)} (ha : StrictLower A)
    (ho : HasTreeOrderAtLeast A b 9) (hM : (onNodes A).card=5)
    (hoff : ∀ x∈supportedNodes A (qdef A), offWeight A b x=0) :
    ∃ t : K, t≠0 ∧ ∀ x∈onNodes A, x≠0 →
      onWeight A b x*nodalSlope (onNodes A) x*fixedRadauT3 x=t := by
  let S := onNodes A
  let T := S.erase 0
  have h0 : (0:K)∈S := zero_mem_onNodes ha
  have hTc : T.card=4 := by
    have hCd : T.card+1=(onNodes A).card := Finset.card_erase_add_one h0
    omega
  let w (x : K) := onWeight A b x*x*fixedRadauT3 x
  have hm (Q : K[X]) (hQ : Q.natDegree+2≤T.card) : ∑ x∈T,w x*Q.eval x=0 := by
    have hdd : (X*radauCubic*Q).natDegree≤6 := by
      have hh := natDegree_mul_le_of_le (natDegree_mul_le_of_le (by simp : (X:K[X]).natDegree≤1)
        radauCubic_degree_le) (show Q.natDegree≤2 from by omega)
      exact hh
    have hEq : row b (evalNodes A (X*radauCubic*Q))=0 :=
      (row_polynomial_eq_unit_primitive ho _ hdd (by decide)).trans
        (radauCubic_weighted_primitive Q (by omega))
    have he : row b (evalNodes A (X*radauCubic*Q)) =
      probe A b 0 (evalNodes A (X*radauCubic*Q)) := by simp [probe]
    rw [he,probe_eq_on_weights hoff] at hEq
    simp only [pow_zero,one_mul,eval_mul,eval_X,radauCubic_eval,←mul_assoc] at hEq
    change ∑ x∈S,w x*Q.eval x=0 at hEq
    have hsum := Finset.sum_erase_add S (fun x => w x*Q.eval x) h0
    change (∑ x∈T,w x*Q.eval x)+_= (∑ x∈S,w x*Q.eval x) at hsum
    rw [hEq] at hsum
    simpa [w] using hsum
  have hex : ∃ x∈T, fixedRadauT3 x≠0 := by
    by_contra! h
    apply radauCubic_ne_zero (K:=K)
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ T
      (fun x hx => by rw [radauCubic_eval,h x hx])
    have hd := radauCubic_degree_le (K:=K)
    omega
  obtain ⟨a,haT,haNZ⟩ := hex
  obtain ⟨ha0,haS⟩ := Finset.mem_erase.mp haT
  let t := w a*nodalSlope T a
  have ht : t≠0 := mul_ne_zero (mul_ne_zero
    (mul_ne_zero (order9_five_on_weights_nonzero ho hM hoff haS) ha0) haNZ) (nodalSlope_ne_zero T a)
  refine ⟨t,ht,?_⟩
  intro x hx hxn
  have hw := nodalSlope_weight_constant T w hm (Finset.mem_erase.mpr ⟨hxn,hx⟩) haT
  rw [nodalSlope_remove_zero S h0 hxn]
  change onWeight A b x*(x*nodalSlope T x)*fixedRadauT3 x=t
  dsimp [w,t] at *
  linear_combination hw

/-- The nonzero weighted state row killing E5 gives the same nodal
slopes at all on coordinates. Its normalization does not require
a sign assumption. -/
theorem five_on_annihilator_weight_norm
    {A : Fin s → Fin s → K} {w : Vec K s}
    (hw : w∈annih (treeSpace A 5))
    (hM : (onNodes A).card=5)
    {P : K[X]} (hPd : P.natDegree≤2)
    (hP : ∀ i, qdef A i≠0 → P.eval (nodes A i)=qdef A i) :
    ∃ t : K, ∀ x∈onNodes A, onWeight A w x*P.eval x*nodalSlope (onNodes A) x=t := by
  let S := onNodes A
  let T := supportedNodes A (qdef A)
  let f (x : K) := onWeight A w x*P.eval x
  have hf (Q : K[X]) (hd : Q.natDegree+2≤S.card) : ∑ x∈S,f x*Q.eval x=0 := by
    change Q.natDegree+2≤(onNodes A).card at hd
    have hQ : Q.natDegree≤3 := by omega
    have hV : diag (qdef A) (evalNodes A Q)∈treeSpace A 5 := by
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
  obtain ⟨a,ha⟩ := Finset.card_pos.mp (by change 0 < (onNodes A).card; omega : 0 < S.card)
  exact ⟨f a*nodalSlope S a,fun x hx => nodalSlope_weight_constant S f hf hx ha⟩

end RKCert.Paired

