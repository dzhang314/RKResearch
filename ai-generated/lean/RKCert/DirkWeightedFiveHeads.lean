module

public import RKCert.FourDebutComplete
public import RKCert.DirkShortTrace

@[expose] public section

/-! # The projected weighted fifth-debut rules

The base is a genuine projected scalar column, allowed to vanish at any
physical row. Zero-base rows stay in every causal-prefix equation. -/
namespace RKCert.Paired.LocalProjection
open RKCert.Endpoint RKCert.OneEscape RKCert.Paired.Pivot Polynomial
open scoped Classical
noncomputable section

structure WeightedFive (K : Type*) [Field K] (s : ℕ) where
  clock : Vec K s
  base : Vec K s
  head : Vec K s
  op : Vec K s →ₗ[K] Vec K s
  pivot : Vec K s
  causal : CausalDiag (Equiv.refl (Fin s)) op pivot
  quadrature : ∀ P : K[X], P.natDegree≤9 → weightedEval clock base P=0 →
    (formalPrimitive P).eval 1=0
  primitive : ∀ j : ℕ, 5≤j → j≤6 → ∀ P q : K[X], P.natDegree≤j →
    q.degree<(j-4:ℕ) →
    op (weightedEval clock base P-weightedEval clock head q) -
      weightedEval clock base (formalPrimitive P) ∈ chain (diag clock) ⊥ head (j-3)
  commutator : ∀ P : K[X], P.natDegree≤5 →
    commutatorR op (diag clock) (weightedEval clock base P) ∈
      chain (diag clock) ⊥ head 3

namespace WeightedFive
variable {K : Type*} [Field K] {s : ℕ}
variable (D : WeightedFive K s)

def sites : Finset K :=
  (Finset.univ.filter fun i => D.base i≠0 ∧ D.clock i≠0).image D.clock

theorem count [CharZero K] : 5≤D.sites.card := by
  classical
  by_contra! h
  let Z := Lagrange.nodal D.sites id
  have hd : Z.natDegree≤4 := by
    change (Lagrange.nodal D.sites id).natDegree≤4
    rw [Lagrange.natDegree_nodal]
    omega
  apply (show Z.Monic from Lagrange.nodal_monic).ne_zero
  apply primitive_shift_detect Z (k:=1) hd 1 one_ne_zero
  intro t
  let P : K[X] := X^(1+t.val)*Z
  have dp : P.natDegree≤9 := natDegree_mul_le.trans (by rw [natDegree_X_pow]; omega)
  apply D.quadrature P dp
  ext i
  rw [weightedEval_apply]
  by_cases hb : D.base i=0
  · simp [hb]
  by_cases hc : D.clock i=0
  · simp [P,hc]
  have hi : D.clock i∈D.sites :=
    Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hb,hc⟩,rfl⟩
  have hz : Z.eval (D.clock i)=0 := Lagrange.eval_nodal_at_node (v:=id) hi
  simp [P,hz]

structure Debut (S : Finset K) (i : Fin s) : Prop where
  active : D.base i≠0
  nz : D.clock i≠0
  fresh : D.clock i∉S
  old : ∀ l < i, D.base l≠0 → D.clock l≠0 → D.clock l∈S

theorem next_debut (S : Finset K) (hcard : S.card<D.sites.card) : ∃ i,D.Debut S i := by
  classical
  obtain ⟨_,hz,hs⟩ := Finset.not_subset.mp
    (show ¬D.sites⊆S from fun h => (not_le_of_gt hcard) (Finset.card_le_card h))
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
  let I := Finset.univ.filter fun l => D.base l≠0 ∧ D.clock l≠0 ∧ D.clock l∉S
  have fi : i∈I := Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2.1,
    (Finset.mem_filter.mp hi).2.2,hs⟩
  have ne : I.Nonempty := ⟨_,fi⟩
  have hp := (Finset.mem_filter.mp (I.min'_mem ne)).2
  refine ⟨I.min' ne,hp.1,hp.2.1,hp.2.2,?_⟩
  intro l hl hb hc
  by_contra hnot
  exact (not_le_of_gt hl) (I.min'_le l
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hb,hc,hnot⟩))

theorem lead (i : Fin s) (x : Vec K s) (h : PrefixZero x i) :
    D.op x i=D.pivot i*x i := D.causal i x h

theorem op_prior {i : Fin s} {x : Vec K s} (h : PrefixZero x i) : PrefixZero (D.op x) i :=
  fun l hl => by rw [D.lead l x (fun t ht => h t (ht.trans hl)),h _ hl,mul_zero]

theorem comm_lead (i : Fin s) (x : Vec K s) (h : PrefixZero x i) :
    commutatorR D.op (diag D.clock) x i= -(D.pivot i)^2*x i := by
  change D.clock i*D.op x i-D.op (diag D.clock x) i-D.op (D.op x) i=_
  have hc : PrefixZero (diag D.clock x) i := fun l hl => by rw [diag_apply,h _ hl,mul_zero]
  rw [D.lead i (diag D.clock x) hc,diag_apply,D.lead i (D.op x) (D.op_prior h),D.lead i x h]
  ring

theorem polynomial_of_chain {x : Vec K s} {n : ℕ}
    (hx : x∈chain (diag D.clock) ⊥ D.head n) :
    ∃ P : K[X], P.degree<(n:WithBot ℕ) ∧ ∀ i,x i=D.head i*P.eval (D.clock i) := by
  obtain ⟨v,hv,P,hP,he⟩ := Clock.exists_head_poly hx
  rw [Submodule.mem_bot] at hv
  subst v
  exact ⟨P,hP,fun i => by simpa [mul_comm] using he i⟩

theorem mask {S : Finset K} {i : Fin s} (db : D.Debut S i) {P : K[X]}
    (h0 : P.eval 0=0) (roots : ∀ a∈S,P.eval a=0) :
    PrefixZero (weightedEval D.clock D.base P) i := by
  intro l hl
  rw [weightedEval_apply]
  by_cases hb : D.base l=0
  · simp [hb]
  by_cases hc : D.clock l=0
  · simp [hc,h0]
  rw [roots _ (db.old _ hl hb hc),zero_mul]

theorem primitive_pay {j : ℕ} (hj : 5≤j) (jh : j≤6) {i : Fin s} {P q : K[X]}
    (dp : P.natDegree≤j) (dq : q.degree<(j-4:ℕ))
    (pre : PrefixZero (weightedEval D.clock D.base P-weightedEval D.clock D.head q) i) :
    ∃ Q : K[X], Q.degree<(j-3:ℕ) ∧
      ∀ l, (l < i ∨ l=i ∧ D.pivot i=0) →
        (formalPrimitive P).eval (D.clock l)*D.base l=D.head l*Q.eval (D.clock l) := by
  obtain ⟨Q,hQ,he⟩ := D.polynomial_of_chain (D.primitive j hj jh P q dp dq)
  refine ⟨-Q,by simpa using hQ,?_⟩
  intro l hl
  have e := he l
  let x := weightedEval D.clock D.base P-weightedEval D.clock D.head q
  have lead0 : D.op x l=0 := by
    rcases hl with hlt|⟨rfl,off⟩
    · exact D.op_prior pre l hlt
    · rw [D.lead _ x pre,off,zero_mul]
  rw [Pi.sub_apply,weightedEval_apply] at e
  change D.op x l-(formalPrimitive P).eval (D.clock l)*D.base l=D.head l*Q.eval (D.clock l) at e
  rw [lead0,zero_sub] at e
  rw [eval_neg,mul_neg,←e,neg_neg]

theorem early_head [CharZero K] {S : Finset K} {i : Fin s} (db : D.Debut S i)
    (small : S.card≤2) : D.head i≠0 := by
  classical
  intro wi
  let H := Lagrange.nodal S id
  have hd : H.natDegree=S.card := Lagrange.natDegree_nodal
  have hz (a : K) (ha : a∈S) : H.eval a=0 := Lagrange.eval_nodal_at_node (v:=id) ha
  have hn : H.eval (D.clock i)≠0 :=
    Lagrange.eval_nodal_not_at_node (fun a ha e => db.fresh (e.symm ▸ ha))
  let V (k : ℕ) : K[X] := X^(1+k)*H
  have pre (k : ℕ) : PrefixZero (weightedEval D.clock D.base (V k)) i :=
    D.mask db (by simp [V]) (fun a ha => by simp [V,hz a ha])
  have vn : weightedEval D.clock D.base (V 0) i≠0 := by
    rw [weightedEval_apply]
    change (X^(1+0)*H).eval _*_≠0
    simpa only [Nat.add_zero,pow_one,eval_mul,eval_X] using
      mul_ne_zero (mul_ne_zero db.nz hn) db.active
  have deg0 : (V 0).natDegree≤5 := natDegree_mul_le.trans (by rw [natDegree_X_pow,hd]; omega)
  obtain ⟨Q,_,rows⟩ := D.polynomial_of_chain (D.commutator (V 0) deg0)
  have e := rows i
  rw [D.comm_lead _ _ (pre 0),wi,zero_mul] at e
  have off : D.pivot i=0 := sq_eq_zero_iff.mp
    (neg_eq_zero.mp ((mul_eq_zero.mp e).resolve_right vn))
  apply (show H.Monic from Lagrange.nodal_monic).ne_zero
  apply primitive_shift_detect H (k:=1) hd.le (D.clock i) db.nz
  intro t
  have dq : (0:K[X]).degree<((5-4:ℕ):WithBot ℕ) := by rw [degree_zero]; exact WithBot.bot_lt_coe _
  have deg : (V t.val).natDegree≤5 := natDegree_mul_le.trans (by rw [natDegree_X_pow,hd]; omega)
  obtain ⟨R,_,eqn⟩ := D.primitive_pay (by decide : 5≤5) (by decide) deg dq (by simpa using pre t.val)
  exact (mul_eq_zero.mp (by simpa [wi] using eqn i (Or.inr ⟨rfl,off⟩))).resolve_right db.active

theorem refund_fifth {S : Finset K} {i : Fin s} (ix : Fin 3→Fin s) (db : D.Debut S i)
    (paid : S.card≤4) (prior : ∀ k,ix k < i) (heads : ∀ k,D.head (ix k)≠0)
    (inj : Function.Injective (D.clock ∘ ix)) : D.pivot i=0 := by
  classical
  let H := Lagrange.nodal S id
  let P : K[X] := X*H
  have hz (a : K) (ha : a∈S) : H.eval a=0 := Lagrange.eval_nodal_at_node (v:=id) ha
  have hd : P.natDegree≤5 :=
    natDegree_mul_le.trans (by rw [natDegree_X,show H.natDegree=S.card from Lagrange.natDegree_nodal]; omega)
  have pre := D.mask db (P:=P) (by simp [P]) (fun a ha => by simp [P,hz a ha])
  have hv : weightedEval D.clock D.base P i≠0 := by
    rw [weightedEval_apply]
    apply mul_ne_zero _ db.active
    rw [show P=X*H from rfl,eval_mul,eval_X]
    exact mul_ne_zero db.nz (Lagrange.eval_nodal_not_at_node (fun a ha e => db.fresh (e.symm ▸ ha)))
  obtain ⟨Q,dQ,rows⟩ := D.polynomial_of_chain (D.commutator P hd)
  have z (k : Fin 3) : Q.eval (D.clock (ix k))=0 := by
    have e := rows (ix k)
    rw [D.comm_lead _ _ (fun l hl => pre l (hl.trans (prior k))),pre _ (prior k),mul_zero] at e
    exact (mul_eq_zero.mp e.symm).resolve_left (heads k)
  have zero : Q=0 := Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero Finset.univ inj.injOn
    (by rw [Finset.card_univ,Fintype.card_fin]; exact dQ) (fun k _ => z k)
  have e := rows i
  rw [D.comm_lead _ _ pre,zero,eval_zero,mul_zero] at e
  exact sq_eq_zero_iff.mp (neg_eq_zero.mp ((mul_eq_zero.mp e).resolve_right hv))

end WeightedFive
end
end RKCert.Paired.LocalProjection
