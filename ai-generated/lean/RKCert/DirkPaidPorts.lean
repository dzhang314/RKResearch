module
public import RKCert.DirkPaidCubic
public import RKCert.DirkQuintic43
@[expose] public section
namespace RKCert.Paired.Terminal.PaidReverseBand
open RKCert.Endpoint Polynomial Module RKCert.OneEscape
variable {K:Type*} [Field K] [CharZero K] {s p H:ℕ} {A:Fin (s+1)→Fin (s+1)→K}
variable {b v:Vec K (s+1)} {P:K[X]}
noncomputable section
set_option maxHeartbeats 2500000

theorem reverse_word_vanish (D:PaidReverseBand A b p H) (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b p)
    (non:¬(dirkBack A b 1).map (diag (mirror A))≤dirkBack A b 1)
    {j:ℕ} (lo:3≤j) (hi:j≤H) {w:Vec K (s+1)} (hw:w∈marked A (p) j)
    (wt:w (Fin.last s)=0) (i:Fin (s+1)) (hτ:tau A b i=0) : w i=0 := by
  have hm:=D.low;have budget:=D.paid
  have hword:=D.to_words (by omega) hi hw wt
  obtain ⟨Q,_,hq⟩:=D.word_polynomial ha ho non (by omega) (by omega) hword
  simp [hq i,hτ]

theorem refund_diagonal (D:PaidReverseBand A b p H) (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b p)
    (non:¬(dirkBack A b 1).map (diag (mirror A))≤dirkBack A b 1)
    {j:ℕ} (lo:1≤j) (hi:j+2≤H) (h:ReverseTrace A b (p) j v P)
    (i:Fin (s+1)) (hτ:tau A b i=0) (vi:v i≠0) (pre:∀k,i < k → v k=0) : A i i=0 := by
  have hm:=D.low;have budget:=D.paid
  have ct:=D.terminal;have col:=D.col
  have wt:commutatorR (transMat A) (diag (mirror A)) v (Fin.last s)=0 := by
    change (mirror A (Fin.last s)*transMat A v (Fin.last s) -
      transMat A _ (Fin.last s))-transMat A _ (Fin.last s)=0
    simp [ReverseHermite.trans_terminal _ col,mirror,ct]
  have hR:=D.reverse_word_vanish ha ho non (by omega) hi (h.commutator ho (by omega)) wt i hτ
  rw [reverse_refund_eq ha i pre] at hR
  exact (pow_eq_zero_iff (by decide : 2≠0)).mp (neg_eq_zero.mp ((mul_eq_zero.mp hR).resolve_right vi))

theorem pivot_primitive (D:PaidReverseBand A b p H) (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b p)
    (non:¬(dirkBack A b 1).map (diag (mirror A))≤dirkBack A b 1)
    {j:ℕ} (lo:2≤j) (hi:j+1≤H) (h:ReverseTrace A b (p) j v P)
    (i:Fin (s+1)) (hb:b i≠0) (hτ:tau A b i=0) (pre:∀k,i < k → v k=0) (ad:A i i=0) :
    (formalPrimitive P).eval (mirror A i)=0 := by
  have hm:=D.low;have budget:=D.paid
  have ct:=D.terminal;have col:=D.col
  have wt:(transMat A v-weightedEval (mirror A) b (formalPrimitive P)) (Fin.last s)=0 := by
    simp [ReverseHermite.trans_terminal _ col,mirror,ct]
  have hh:=D.reverse_word_vanish ha ho non (by omega) hi
    ((h.primitive ho (by omega)).pure) wt i hτ
  rw [Pi.sub_apply,reverse_at ha i pre,ad,zero_mul,zero_sub,neg_eq_zero,weightedEval_apply] at hh
  exact (mul_eq_zero.mp hh).resolve_right hb

/-- The first actual nonzero coordinate in reverse chronology earns a
diagonal refund and every remaining scalar primitive test, not just a
matching ansatz. -/
theorem physical_reverse_pivot (D:PaidReverseBand A b p H) (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b p)
    (non:¬(dirkBack A b 1).map (diag (mirror A))≤dirkBack A b 1)
    {j:ℕ} (lo:2≤j) (hi:j+2≤H) (h:ReverseTrace A b (p) j v P)
    (active:∀i,v i≠0 → b i≠0 ∧ tau A b i=0) (hP:P≠0) :
    ∃i:Fin (s+1), v i≠0 ∧ b i≠0 ∧ tau A b i=0 ∧ A i i=0 ∧
      ∀k:ℕ,j+k+1≤H → (formalPrimitive (X^k*P)).eval (mirror A i)=0 := by
  have hm:=D.low;have budget:=D.paid
  have nz:v≠0:=by
    intro hz
    rw [hz] at h
    exact hP (rev_zero_numeric h ho (by omega))
  obtain ⟨i,vi,pre⟩:=exists_last_coordinate nz
  obtain ⟨bi,τi⟩:=active i vi
  have ad:=D.refund_diagonal ha ho non (by omega) hi h i τi vi pre
  refine ⟨i,vi,bi,τi,ad,?_⟩
  intro k hk
  have h':=rev_clock_pow h k (by omega)
  exact D.pivot_primitive ha ho non (by omega) hk h' i bi τi
    (fun l hl=>by simp [timesY,pre l hl]) ad
/-- True marked-left/ordinary-right products: the only additional terminal
zero needed is the actual defect's own last entry, to cover the weighted
image. Locality and the reverse head shape come from the paid band. -/
theorem port_contrast (D:PaidReverseBand A b p H) (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b p)
    {j:ℕ} (lo:3≤j) (hi:j+3≤H) (hv:v∈zeroSpace A j) (vt:v (Fin.last s)=0) :
    ∃Q:K[X], Q.natDegree≤j ∧ (∀i,tau A b i≠0→v i=Q.eval (mirror A i)) ∧
      (∀i,tau A b i=0→b i*v i=0) ∧
      ∃θ:Vec K (s+1),ReverseTrace A b p j θ Q ∧ (∀i,θ i≠0→b i≠0 ∧ tau A b i=0):=by
  have hp:=D.paid;have hm:=D.low
  have nloc:=D.nonlocal_cubic ha ho
  have td:tau A b∈dirkBack A b 1:=by rw [D.one];exact Submodule.subset_span (Set.mem_singleton _)
  have t0:tau A b∈ReverseHermite.zeroMarked A p (Fin.last s) 3:=by
    rw [D.cover 3 (by decide) (by omega)];exact td
  have tlast:tau A b (Fin.last s)=0:=t0.2
  have wt:tau A b*v∈dirkBack A b (3+j-2):=D.to_words (j:=3+j) (by omega) (by omega)
    (marked_mul_tree (j:=3) (k:=j) (by omega) t0.1 (zeroSpace_le_treeSpace A j hv)) (by simp [tlast])
  have wb:b*v∈dirkBack A b (j-2):=D.to_words (j:=j) (by omega) (by omega) (weights_mul_zeroSpace ho (by omega) hv) (by simp [vt])
  obtain ⟨Q,qd,eqn⟩:=D.word_polynomial ha ho nloc (r:=3+j-2) (by omega) (by omega) wt
  obtain ⟨L,_,eqw⟩:=D.word_polynomial ha ho nloc (r:=j-2) (by omega) (by omega) wb
  have fit(i:Fin (s+1)) (active:tau A b i≠0):v i=Q.eval (mirror A i):=by
    apply mul_left_cancel₀ active
    rw [mul_comm (tau A b i) (Q.eval _)]
    exact eqn i
  have deg:Q.natDegree≤j:=by
    by_cases zero:Q=0
    · simp [zero]
    have bound:Q.natDegree<3+j-2:=(natDegree_lt_iff_degree_lt zero).mpr qd
    omega
  refine ⟨Q,deg,fit,fun i z=>by simpa [z] using eqw i,weightedEval (mirror A) b Q-b*v,
    (ReverseTrace.scalar A b deg).sub_pure (weights_mul_zeroSpace ho (by omega) hv),?_⟩
  intro i act
  refine ⟨?_,?_⟩
  · intro z;apply act;simp [z]
  · by_contra nz;apply act;simp [fit i nz,mul_comm]

/-- Two genuine original reverse pivots with their actual diagonal refunds,
first and next primitive families priced separately, before the terminal
word cutoff. -/
theorem two_paid_ports (D:PaidReverseBand A b p H) (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b p)
    {j:ℕ} (lo:2≤j) (hi:j+4≤H) (h:ReverseTrace A b p j v P) (nz:P≠0)
    (active:∀i,v i≠0→b i≠0 ∧ tau A b i=0) :
    ∃i l:Fin (s+1),let u:=mirror A i;let z:=mirror A l
      b i≠0 ∧ tau A b i=0 ∧ b l≠0 ∧ tau A b l=0 ∧ u≠0 ∧ z≠0 ∧ z≠u ∧
      (∀k:ℕ,j+k+2≤H→ (Paired.primitive (X^(k+1)*P)).eval u=0) ∧
      ∀k:ℕ,j+k+3≤H→ (Paired.primitive (X^(k+1)*((X-C u)*P))).eval z=0:=by
  have hm:=D.low;have hp:=D.paid
  let y:=mirror A
  let x:=diag y v
  have tr:ReverseTrace A b p (j+1) x (X*P):=h.clock (by omega)
  have on(i:Fin (s+1)) (xi:x i≠0):y i≠0 ∧ v i≠0:=mul_ne_zero_iff.mp xi
  have ac(i:Fin (s+1)) (xi:x i≠0):=active i (on i xi).2
  obtain ⟨i,xi,bi,ti,_,first⟩:=D.physical_reverse_pivot ha ho (D.nonlocal_cubic ha ho) (by omega) (by omega) tr
    ac (mul_ne_zero X_ne_zero nz)
  let u:=y i
  let a:=diag y x-u • x
  let Q:=X*(X*P)-u • (X*P)
  have eqn:Q=(X-C u)*(X*P):=by simp only [Q,Polynomial.smul_eq_C_mul,sub_mul]
  have tr2:ReverseTrace A b p (j+1+1) a Q:=rev_shift tr u (by omega)
  have on2(l:Fin (s+1))(ll:a l≠0):y l≠u ∧ x l≠0:=by
    have e:a l=(y l-u)*x l:=by simp [a,diag_apply,sub_mul]
    rw [e] at ll
    exact ⟨sub_ne_zero.mp (mul_ne_zero_iff.mp ll).1,(mul_ne_zero_iff.mp ll).2⟩
  obtain ⟨l,al,bl,tl,_,next⟩:=D.physical_reverse_pivot ha ho (D.nonlocal_cubic ha ho) (by omega) (by omega) tr2
    (fun l hh=>ac _ (on2 _ hh).2) (by rw [eqn];exact mul_ne_zero (X_sub_C_ne_zero _) (mul_ne_zero X_ne_zero nz))
  refine ⟨i,l,bi,ti,bl,tl,(on i xi).1,(on l (on2 l al).2).1,(on2 l al).1,?_,?_⟩
  · intro k hk
    have f:=first k (by omega)
    rwa [←mul_assoc,←pow_succ,formalPrimitive_eq_treePrimitive] at f
  · intro k hk
    have f:=next k (by omega)
    have e:X^k*Q=X^(k+1)*((X-C u)*P):=by rw [eqn,pow_succ];ring
    rwa [e,formalPrimitive_eq_treePrimitive] at f

/-- The full physical quartic is jointly hidden on both output marks;
this statement erases no RK stage. -/
theorem quartic_jointly_hidden (D:PaidReverseBand A b p H) (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b p)
    (enough:9≤H) (hv:v∈zeroSpace A 4) (vt:v (Fin.last s)=0):b*v=0 ∧ tau A b*v=0:=by
  obtain ⟨Q,dq,fit,off,θ,tr,ac⟩:=D.port_contrast ha ho (by decide) (by omega) hv vt
  have zero:Q=0:=by
    by_contra nz
    obtain ⟨i,l,_,_,_,_,un,vn,vu,first,second⟩:=D.two_paid_ports ha ho (by decide) (by omega) tr nz ac
    exact nz (RKCert.EndpointPhysical.quintic_four_three Q (by omega) un vn vu
      (fun k=>first k.val (by have:=k.isLt;omega)) (fun k=>second k.val (by have:=k.isLt;omega)))
  have on(i:Fin (s+1)) (hh:tau A b i≠0):v i=0:=by simpa [zero] using fit i hh
  constructor <;> ext i
  · by_cases hh:tau A b i=0
    · exact off i hh
    · simp [on i hh]
  · by_cases hh:tau A b i=0
    · simp [hh]
    · simp [on i hh]
end
end RKCert.Paired.Terminal.PaidReverseBand

