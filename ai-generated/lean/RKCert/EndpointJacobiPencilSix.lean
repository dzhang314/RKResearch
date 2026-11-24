module

public import RKCert.EndpointJacobiLowering
public import RKCert.AffinePencilMultiplicity
public import Mathlib.FieldTheory.IsAlgClosed.Basic

@[expose] public section

/-! # The free degree-seven pencil always has at least six distinct roots

This uses the one nonzero affine lowering remainder directly rather than
an arithmetic discriminant. It treats the fixed degree-six polynomial too.
-/
namespace RKCert.Paired
open Polynomial RKCert.FixedPolynomial
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

theorem jacobiTwo_zero_eq_one : jacobiTwo K 0=1 :=
  (jacobiTwo_monic 0).natDegree_eq_zero.mp (jacobiTwo_degree 0)

private theorem jacobiTwo_first_recurrence :
    ∃ a b : K,b≠0 ∧ X*jacobiTwo K 1=jacobiTwo K 2+C a*jacobiTwo K 1+C b*jacobiTwo K 0 := by
  let P := X*jacobiTwo K 1-jacobiTwo K 2
  let a := P.coeff 1
  let R := P-C a*jacobiTwo K 1
  have pd : P.natDegree≤1 := jacobiTwo_raise_diff 1
  have rd : R.natDegree=0 := Nat.eq_zero_of_le_zero (jacobiTwo_strip (by decide : 0<1) pd)
  let b := R.coeff 0
  have re : R=C b := eq_C_of_natDegree_eq_zero rd
  have eq : X*jacobiTwo K 1=jacobiTwo K 2+C a*jacobiTwo K 1+C b*jacobiTwo K 0 := by
    rw [jacobiTwo_zero_eq_one,mul_one]
    change X*jacobiTwo K 1-jacobiTwo K 2-C a*jacobiTwo K 1=C b at re
    linear_combination re
  refine ⟨a,b,?_,eq⟩
  intro bz
  have test : jacobiPair (X*jacobiTwo K 1) (jacobiTwo K 0)=0 := by
    rw [eq,jacobiPair_add,jacobiPair_add,jacobiPair_C_mul,jacobiPair_C_mul,bz,zero_mul,
      jacobiPair_orthogonal _ _ (by rw [jacobiTwo_degree]; decide),
      jacobiPair_orthogonal _ _ (by rw [jacobiTwo_degree]; decide),mul_zero,add_zero,add_zero]
  rw [jacobiPair_mul_X,jacobiTwo_zero_eq_one,mul_one,
    jacobiPair_top_coeff 1 (by decide) (by rw [natDegree_X]),coeff_X_one,one_mul] at test
  exact jacobiTwo_diagonal_ne 1 test

theorem jacobiTwo_recurrence_pos (n : ℕ) (pos : 0<n) :
    ∃ a b : K,b≠0 ∧
      X*jacobiTwo K n=jacobiTwo K (n+1)+C a*jacobiTwo K n+C b*jacobiTwo K (n-1) := by
  by_cases e : n=1
  · subst n
    exact jacobiTwo_first_recurrence
  · exact jacobiTwo_three_term n (by omega)

theorem jacobiTwo_adjacent_coprime (n : ℕ) :
    IsCoprime (jacobiTwo K (n+1)) (jacobiTwo K n) := by
  induction n with
  | zero => rw [jacobiTwo_zero_eq_one]; exact isCoprime_one_right
  | succ n ih =>
    obtain ⟨a,b,bn,rec⟩ := jacobiTwo_recurrence_pos (K:=K) (n+1) (by omega)
    let J := jacobiTwo K (n+1)
    let L := jacobiTwo K n
    let P := jacobiTwo K (n+1+1)
    change X*J=P+C a*J+C b*L at rec
    obtain ⟨u,v,uv⟩ := ih
    change u*J+v*L=1 at uv
    have bv : C b⁻¹*C b=1 := by rw [←map_mul,inv_mul_cancel₀ bn,map_one]
    have eq : C b⁻¹*(X*J-P-C a*J)=L := by
      have x : X*J-P-C a*J=C b*L := by linear_combination rec
      rw [x,←mul_assoc,bv,one_mul]
    refine ⟨-(v*C b⁻¹), u+v*C b⁻¹*(X-C a),?_⟩
    change -(v*C b⁻¹)*P+(u+v*C b⁻¹*(X-C a))*J=1
    linear_combination (norm := ring) v*eq+uv

theorem jacobiTwo_fixed_simple (n : ℕ) (hn : 2≤n) :
    (jacobiTwo K n).roots.Nodup := by
  let J := jacobiTwo K n
  let L := jacobiTwo K (n-1)
  obtain ⟨a,b,bn,rec⟩ := jacobiTwo_three_term (K:=K) n hn
  obtain ⟨m,low⟩ := jacobiTwo_lowering n hn a b rec
  have co : IsCoprime J L := by
    have e := jacobiTwo_adjacent_coprime (K:=K) (n-1)
    rw [Nat.sub_add_cancel (by omega : 1≤n)] at e
    exact e
  have Jne : J≠0 := (jacobiTwo_monic _).ne_zero
  apply Multiset.nodup_iff_count_le_one.mpr
  intro u
  rw [count_roots]
  by_contra! bad
  obtain ⟨q0,q1⟩ := (one_lt_rootMultiplicity_iff_isRoot Jne).mp bad
  change J.eval u=0 at q0
  change J.derivative.eval u=0 at q1
  have s : L.eval u≠0 := by
    obtain ⟨e,f,ef⟩ := co
    intro z
    have h := congrArg (eval u) ef
    simp only [eval_add,eval_mul,eval_one,q0,z,mul_zero,add_zero] at h
    exact zero_ne_one h
  have z := congrArg (eval u) low
  change (jacobiWeight K*J.derivative).eval u=
    ((C m-C (n:K)*X)*J+C ((2*(n:K)+3)*b)*L).eval u at z
  simp only [eval_add,eval_mul,q0,q1,mul_zero,zero_add,eval_C] at z
  exact (mul_ne_zero (mul_ne_zero (by
    have h : (2*n+3:ℕ)≠0 := by omega
    exact_mod_cast h) bn) s) z.symm

set_option maxHeartbeats 1700000 in
theorem jacobiTwo_seven_pencil_distinct [IsAlgClosed K] (a : K) :
    6≤(jacobiTwo K 7+C a*jacobiTwo K 6).roots.toFinset.card := by
  let J := jacobiTwo K 7
  let L := jacobiTwo K 6
  let T := jacobiTwo K 5
  let F := J+C a*L
  have df : F.natDegree=7 := by
    change (J+C a*L).natDegree=7
    have b := natDegree_C_mul_le a L
    have hJ : J.natDegree=7 := jacobiTwo_degree 7
    have hL : L.natDegree=6 := jacobiTwo_degree 6
    have lt : (C a*L).natDegree<J.natDegree := by omega
    exact (natDegree_add_eq_left_of_natDegree_lt lt).trans hJ
  have fn : F≠0 := fun e => by rw [e,natDegree_zero] at df; contradiction
  by_cases az : a=0
  · have e : F=J := by simp [F,az]
    change 6≤F.roots.toFinset.card
    rw [e,Multiset.toFinset_card_of_nodup (jacobiTwo_fixed_simple 7 (by decide))]
    have h := (IsAlgClosed.splits J).natDegree_eq_card_roots
    change 6≤J.roots.card
    rw [←h]
    change 6≤(jacobiTwo K 7).natDegree
    rw [jacobiTwo_degree]
    decide
  have co : IsCoprime F L := by
    obtain ⟨p,q,pq⟩ := jacobiTwo_adjacent_coprime (K:=K) 6
    refine ⟨p,q-p*C a,?_⟩
    change p*(J+C a*L)+(q-p*C a)*L=1
    change p*J+q*L=1 at pq
    linear_combination pq
  obtain ⟨c,b,bn,rl⟩ := jacobiTwo_three_term (K:=K) 6 (by decide)
  obtain ⟨d,t,tn,rj⟩ := jacobiTwo_three_term (K:=K) 7 (by decide)
  obtain ⟨m,hL⟩ := jacobiTwo_lowering 6 (by decide) c b rl
  obtain ⟨u,hJ⟩ := jacobiTwo_lowering 7 (by decide) d t rj
  change X*L=J+C c*L+C b*T at rl
  let W := jacobiWeight K
  have el : W*L.derivative=(C m-C (6:K)*X)*L+C (15:K)*C b*T := by
    norm_num at hL; exact hL
  have ej : W*J.derivative=(C u-C (7:K)*X)*J+C (17:K)*C t*L := by
    norm_num at hJ; exact hJ
  let U := C (u-15*a)-C (7:K)*X
  let V := C (16*a)*X+C (17*t+a*(m-15*c)-a*(u-15*a))
  have Vdegree : V.natDegree≤1 := (natDegree_add_le _ _).trans
    (max_le ((natDegree_C_mul_le _ _).trans (by rw [natDegree_X])) (by rw [natDegree_C]; decide))
  have vn : V≠0 := by
    intro z
    have e := congrArg (fun P : K[X] => P.coeff 1) z
    change (C (16*a)*X+C (17*t+a*(m-15*c)-a*(u-15*a))).coeff 1=0 at e
    rw [coeff_add,coeff_C_mul,coeff_X_one,mul_one,coeff_C,ite_eq_right (by decide : (1:ℕ)≠0),add_zero] at e
    exact (mul_ne_zero (by norm_num : (16:K)≠0) az) e
  have diff : W*F.derivative=U*F+V*L := by
    change W*(J+C a*L).derivative=U*(J+C a*L)+V*L
    rw [map_add,derivative_C_mul]
    rw [show W*(J.derivative+C a*L.derivative)=W*J.derivative+C a*(W*L.derivative) by ring,el,ej]
    simp only [U,V,map_sub,map_add,map_mul,C_ofNat]
    linear_combination -((15:K[X])*C a)*rl
  have bound := distinct_roots_of_affine_lowering fn (IsAlgClosed.splits F) co vn Vdegree diff
  have d : F.natDegree=7 := df
  change 6≤F.roots.toFinset.card
  omega

end
end RKCert.Paired
