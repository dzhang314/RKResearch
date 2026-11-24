module
public import RKCert.DirkWeightedFourInterface
public import RKCert.FourDebutComplete
@[expose] public section
namespace RKCert.Paired.LocalProjection.WeightedFour
open RKCert.Endpoint Polynomial RKCert.OneEscape
open scoped Classical
variable {K:Type*} [Field K] {s:ℕ}
noncomputable section

def sites (D:WeightedFour K s) : Finset K :=
  (Finset.univ.filter fun i=>D.base i≠0 ∧ D.clock i≠0).image D.clock

theorem count [CharZero K] (D:WeightedFour K s) : 4≤D.sites.card := by
  classical
  by_contra! h
  let Z:=Lagrange.nodal D.sites id
  have hd:Z.natDegree≤3 := by change (Lagrange.nodal D.sites id).natDegree≤3; rw [Lagrange.natDegree_nodal]; omega
  apply (show Z.Monic from Lagrange.nodal_monic).ne_zero
  apply primitive_shift_detect Z (k:=1) hd 1 one_ne_zero
  intro t
  let P:K[X]:=X^(1+t.val)*Z
  have dp:P.natDegree≤7 := natDegree_mul_le.trans (by rw [natDegree_X_pow]; omega)
  have hval:weightedEval D.clock D.base P=0 := by
    ext i
    rw [weightedEval_apply]
    by_cases hb:D.base i=0
    · simp [hb]
    by_cases hc:D.clock i=0
    · simp [P,hc]
    have hi:D.clock i∈D.sites := Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hb,hc⟩,rfl⟩
    have hz:Z.eval (D.clock i)=0 := Lagrange.eval_nodal_at_node (v:=id) hi
    simp [P,hz]
  simpa only [hval,row_apply,Pi.zero_apply,zero_mul,Finset.sum_const_zero] using (D.quadrature P dp).symm

structure Debut (D:WeightedFour K s) (S:Finset K) (i:Fin s) : Prop where
  active : D.base i≠0
  nz : D.clock i≠0
  fresh : D.clock i∉S
  old : ∀l, i < l → D.base l≠0 → D.clock l≠0 → D.clock l∈S

variable (D:WeightedFour K s)
theorem next_debut (S:Finset K) (count:S.card<D.sites.card) : ∃i,Debut D S i := by
  classical
  obtain ⟨_,hz,hs⟩:=Finset.not_subset.mp (show ¬D.sites⊆S from fun h=>(not_le_of_gt count) (Finset.card_le_card h))
  obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hz
  let F:=Finset.univ.filter fun l=>D.base l≠0 ∧ D.clock l≠0 ∧ D.clock l∉S
  have fi:i∈F:=Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2.1,(Finset.mem_filter.mp hi).2.2,hs⟩
  have ne:F.Nonempty:=⟨i,fi⟩
  have h:=(Finset.mem_filter.mp (F.max'_mem ne)).2
  refine ⟨F.max' ne,h.1,h.2.1,h.2.2,?_⟩
  intro l hl hb hc
  by_contra hnot
  exact (not_le_of_gt hl) (F.le_max' l (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hb,hc,hnot⟩))

def PriorZero (x:Vec K s) (i:Fin s) : Prop := ∀l, i < l → x l=0
def pivot (i:Fin s):K:=D.op (Pi.single i 1) i

theorem lead (i:Fin s) (x:Vec K s) (h:PriorZero x i) : D.op x i=D.pivot i*x i := by
  classical
  have e:=D.causal i x (x i • Pi.single i 1) (fun l hl=>by
    rcases eq_or_lt_of_le hl with e|e
    · subst l; simp
    · simp [ne_of_gt e,h l e])
  simpa [pivot,mul_comm] using e

theorem op_prior {i:Fin s} {x:Vec K s} (h:PriorZero x i) : PriorZero (D.op x) i :=
  fun l hl=>by rw [D.lead l x (fun t ht=>h t (hl.trans ht)),h _ hl,mul_zero]

theorem comm_lead (i:Fin s) (x:Vec K s) (h:PriorZero x i) :
    commutatorR D.op (diag D.clock) x i= -(D.pivot i)^2*x i := by
  change D.clock i*D.op x i - D.op (diag D.clock x) i - D.op (D.op x) i=_
  have hc:PriorZero (diag D.clock x) i:=fun l hl=>by rw [diag_apply,h _ hl,mul_zero]
  rw [D.lead i (diag D.clock x) hc,diag_apply,D.lead i (D.op x) (D.op_prior h),D.lead i x h]
  ring

theorem polynomial_of_chain {x:Vec K s} {n:ℕ} (hx:x∈chain (diag D.clock) ⊥ D.head n) :
    ∃P:K[X],P.degree<(n:WithBot ℕ) ∧ ∀i,x i=D.head i*P.eval (D.clock i) := by
  obtain ⟨v,hv,P,hP,he⟩:=Clock.exists_head_poly hx
  rw [Submodule.mem_bot] at hv
  subst v
  exact ⟨P,hP,fun i=>by simpa [mul_comm] using he i⟩

theorem mask {S:Finset K} {i:Fin s} (db:Debut D S i) {P:K[X]} (h0:P.eval 0=0) (roots:∀a∈S,P.eval a=0) :
    PriorZero (weightedEval D.clock D.base P) i := by
  intro l hl
  rw [weightedEval_apply]
  by_cases hb:D.base l=0
  · simp [hb]
  by_cases hc:D.clock l=0
  · simp [hc,h0]
  rw [roots _ (db.old _ hl hb hc),zero_mul]

theorem primitive_cut {j:ℕ} (hj:3≤j) (jh:j≤5) {i:Fin s} (off:D.pivot i=0) {P q:K[X]}
    (dp:P.natDegree≤j) (dq:q.degree<(j-3:ℕ)) (pre:PriorZero (weightedEval D.clock D.base P-weightedEval D.clock D.head q) i) :
    ∃Q:K[X],Q.degree<(j-2:ℕ) ∧ ∀l,i ≤ l → (formalPrimitive P).eval (D.clock l)*D.base l=D.head l*Q.eval (D.clock l) := by
  obtain ⟨Q,hQ,he⟩:=D.polynomial_of_chain (D.primitive j hj jh P q dp dq)
  refine ⟨-Q,by simpa using hQ,?_⟩
  intro l hl
  have e:=he l
  let x:=weightedEval D.clock D.base P-weightedEval D.clock D.head q
  have lead0:D.op x l=0 := by
    rcases eq_or_lt_of_le hl with rfl|hlt
    · rw [D.lead i x pre,off,zero_mul]
    · exact D.op_prior pre l hlt
  rw [Pi.sub_apply,weightedEval_apply] at e
  change D.op x l - (formalPrimitive P).eval (D.clock l)*D.base l=D.head l*Q.eval (D.clock l) at e
  rw [lead0,zero_sub] at e
  rw [eval_neg,mul_neg,←e,neg_neg]

theorem early_head [CharZero K] {S:Finset K} {i:Fin s} (db:Debut D S i) (small:S.card≤2) : D.head i≠0 := by
  classical
  intro wi
  let H:=Lagrange.nodal S id
  have hd:H.natDegree=S.card:=Lagrange.natDegree_nodal
  have hz (a:K) (ha:a∈S):H.eval a=0:=Lagrange.eval_nodal_at_node (v:=id) ha
  have hn:H.eval (D.clock i)≠0:=Lagrange.eval_nodal_not_at_node (fun a ha e=>db.fresh (e.symm ▸ ha))
  let V (k:ℕ):K[X]:=X^(1+k)*H
  have pre (k:ℕ):PriorZero (weightedEval D.clock D.base (V k)) i :=
    D.mask db (by simp [V]) (fun a ha=>by simp [V,hz a ha])
  have vn:weightedEval D.clock D.base (V 0) i≠0 := by
    rw [weightedEval_apply]; change (X^(1+0)*H).eval _*_≠0
    simpa only [Nat.add_zero,pow_one,eval_mul,eval_X] using mul_ne_zero (mul_ne_zero db.nz hn) db.active
  have deg0:(V 0).natDegree≤3:=natDegree_mul_le.trans (by rw [natDegree_X_pow,hd]; omega)
  obtain ⟨Q,_,row⟩:=D.polynomial_of_chain (D.commutator 3 (by decide) (by decide) (V 0) deg0)
  have e:=row i
  rw [D.comm_lead _ _ (pre 0),wi,zero_mul] at e
  have off:D.pivot i=0:=sq_eq_zero_iff.mp (neg_eq_zero.mp ((mul_eq_zero.mp e).resolve_right vn))
  apply (show H.Monic from Lagrange.nodal_monic).ne_zero
  apply primitive_shift_detect H (k:=1) hd.le (D.clock i) db.nz
  intro t
  have dq:(0:K[X]).degree<(5-3:ℕ):=by rw [degree_zero]; exact WithBot.bot_lt_coe _
  have deg:(V t.val).natDegree≤5:=natDegree_mul_le.trans (by rw [natDegree_X_pow,hd]; omega)
  obtain ⟨R,_,eqn⟩:=D.primitive_cut (by decide:3≤5) (by decide) off deg dq (by simpa using pre t.val)
  exact (mul_eq_zero.mp (by simpa [wi] using eqn i le_rfl)).resolve_right db.active

theorem general_refund {S:Finset K} {i:Fin s} {j n:ℕ} (ix:Fin n→Fin s) (db:Debut D S i) (hj:3≤j) (jh:j≤4)
    (paid:S.card+1≤j) (hn:j-1=n) (prior:∀k,i < ix k) (heads:∀k,D.head (ix k)≠0) (inj:Function.Injective (D.clock ∘ ix)) :
    D.pivot i=0 := by
  classical
  let H:=Lagrange.nodal S id
  let P:K[X]:=X*H
  have hz (a:K) (ha:a∈S):H.eval a=0:=Lagrange.eval_nodal_at_node (v:=id) ha
  have hd:P.natDegree≤j:=natDegree_mul_le.trans (by rw [natDegree_X,show H.natDegree=S.card from Lagrange.natDegree_nodal]; omega)
  have pre:=D.mask db (P:=P) (by simp [P]) (fun a ha=>by simp [P,hz a ha])
  have hv:weightedEval D.clock D.base P i≠0 := by
    rw [weightedEval_apply]; apply mul_ne_zero _ db.active
    rw [show P=X*H from rfl,eval_mul,eval_X]
    exact mul_ne_zero db.nz (Lagrange.eval_nodal_not_at_node (fun a ha e=>db.fresh (e.symm ▸ ha)))
  obtain ⟨Q,degree,row⟩:=D.polynomial_of_chain (D.commutator j hj jh P hd)
  have z (k:Fin n):Q.eval (D.clock (ix k))=0 := by
    have e:=row (ix k)
    rw [D.comm_lead _ _ (fun l hl=>pre l ((prior k).trans hl)),pre _ (prior k),mul_zero] at e
    exact (mul_eq_zero.mp e.symm).resolve_left (heads k)
  have zero:Q=0:=Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero Finset.univ inj.injOn
    (by rw [Finset.card_univ,Fintype.card_fin,←hn]; exact degree) (fun k _=>z k)
  have e:=row i
  rw [D.comm_lead _ _ pre,zero,eval_zero,mul_zero] at e
  exact sq_eq_zero_iff.mp (neg_eq_zero.mp ((mul_eq_zero.mp e).resolve_right hv))

end
end RKCert.Paired.LocalProjection.WeightedFour
