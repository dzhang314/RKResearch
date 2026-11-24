module
public import RKCert.DirkMidpointGridIdeal
public import RKCert.CoreSupport
@[expose] public section
namespace RKCert.Paired.Terminal.MidpointHead
open Polynomial Module RKCert.OneEscape RKCert.Endpoint
variable {K:Type*} [Field K] [CharZero K] {s m r:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b w:Vec K (s+1)} {U:Submodule K (Vec K (s+1))}
noncomputable section

/-- Every node-local product of two genuine grade-five columns lands in
the invariant core, even though all grade-ten scalars need not split
off by the naive full moment budget. -/
theorem local_product_to_core (h:MidpointHead A m U w r) (hm:m=7 ∨ m=8)
    (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b (2*m)) (he:s+1+3=3*m)
    {v t:Vec K (s+1)} (hv:v∈zeroSpace A 5) (ht:t∈zeroSpace A 5)
    {a:K} (support:∀i,nodes A i≠a → (v*t) i=0) : v*t∈U :=by
  let fix : m=7 ∨ m=8 ∨ m=9 ∨ m=10 := hm.imp_right Or.inl
  have low:7≤m:=by rcases hm with rfl|rfl <;>decide
  have up:m≤8:=by rcases hm with rfl|rfl <;>decide
  let c:=nodes A
  have product : v*t∈zeroSpace A 10 := zeroSpace_mul (A:=A) (m:=5) (n:=5) (v:=v) (w:=t) hv ht
  obtain ⟨H,x,hx,tail,rep⟩:=h.pure_decompose hm ha ho he (q:=10) (by omega) (by omega)
    product (fun i clean=>by rw [Pi.mul_apply,clean v hv,zero_mul])
  have kill(i:Fin (s+1)) : (c i-a)*(v*t) i=0 :=by
    by_cases eqn:c i=a
    · rw [eqn,sub_self,zero_mul]
    · rw [support i eqn,mul_zero]
  let Q:K[X]:=X-C a
  have dq:Q.natDegree=1:=natDegree_X_sub_C _
  have num:evalNodes A (Q*H) = -weightedEval c x Q :=by
    ext i
    have eqn:=congrFun rep i
    have z:=kill i
    change (v*t) i=H.eval (c i)+x i at eqn
    rw [eqn] at z
    simp only [Q,evalNodes_apply,eval_mul,eval_sub,eval_X,eval_C,Pi.neg_apply,weightedEval_apply]
    change (c i-a)*H.eval (c i)= -((c i-a)*x i)
    linear_combination z
  have grid:(X-1)*lobatto m ∣ Q*H:=by
    apply h.grid_dvd_of_pure_polynomial fix ha ho he (q:=11) (by omega) (by omega)
    · have:=tail.degree;exact natDegree_mul_le.trans (by omega)
    · rw [num]
      apply Submodule.neg_mem
      have y:=orbit_mul_polynomial h.invariant (by have:=h.positive;omega) hx Q
      simpa only [dq,show r+(10-5)+1=r+(11-5) by omega] using y
  have zH:=lobatto_tail_linear hm (by simpa only [show 2*m-10-1=2*m-11 by omega] using tail) a grid
  have vx:v*t=x:=by rw [rep,zH,show evalNodes A (0:K[X])=0 from by ext i;simp,zero_add]
  have sites:=h.physical_head_site_bound fix ha ho he (q:=2*m-3) (by omega) (by omega)
  apply Clock.localized_mem h.invariant h.normalized (by omega:r+(10-5)<(Clock.headSites (nodes A) w).card)
  · rw [vx];exact hx
  · exact support

/-- This is closure under actual physical coordinate multiplication by
every genuine F5 element, not a claim about stage compression. -/
theorem core_times_five (h:MidpointHead A m U w r) (hm:m=7 ∨ m=8)
    (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b (2*m)) (he:s+1+3=3*m)
    {u v:Vec K (s+1)} (hu:u∈U) (hv:v∈zeroSpace A 5) : u*v∈U :=by
  classical
  have eqn:u*v=∑ z∈Clock.sites (nodes A),Clock.fiber (nodes A) z u*v :=by rw [←Finset.sum_mul,Clock.sum_fibers]
  rw [eqn]
  apply U.sum_mem
  intro z _
  apply h.local_product_to_core hm ha ho he (h.paid (Clock.fiber_mem h.invariant z hu)) hv (a:=z)
  intro i hi
  simp [Clock.fiber,hi]

/-- Subtract the actual unit on the core's physical support from the
head. All genuine degree and coefficient ranks remain the same. -/
theorem disjoint_midpoint_head (h:MidpointHead A m U w r) (hm:m=7 ∨ m=8)
    (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b (2*m)) (he:s+1+3=3*m) :
    ∃w':Vec K (s+1), MidpointHead A m U w' r ∧
      (∀i,Clock.Live U i → w' i=0) ∧ Clock.MulClosed U :=by
  classical
  have seven:7≤m:=by rcases hm with rfl|rfl <;>decide
  have mul:Clock.MulClosed U:=fun u hu v hv=>h.core_times_five hm ha ho he hu (h.paid hv)
  obtain ⟨y,_,cut,same⟩:=Clock.disjoint_head h.invariant mul
    (fun _ hu=>h.core_times_five hm ha ho he hu (h.head_paid (by omega)))
  refine ⟨y,⟨h.positive,h.invariant,h.paid,h.largest,h.lower,h.upper,h.count,?_,?_⟩,cut,mul⟩
  · intro a incl
    ext i
    by_cases non:Clock.fiber (nodes A) a y i=0
    · exact non
    · have z:=cut i ⟨_,incl,non⟩
      simp [Clock.fiber,z] at non
  · intro j lo hi
    rw [same,h.band j lo hi]

end
end RKCert.Paired.Terminal.MidpointHead

