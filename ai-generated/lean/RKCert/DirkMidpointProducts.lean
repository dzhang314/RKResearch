module
public import RKCert.DirkActualTreeHead
public import RKCert.LobattoPaidTails
@[expose] public section
namespace RKCert.Paired.Terminal.MidpointHead
open Polynomial Module RKCert.OneEscape RKCert.Endpoint
variable {K:Type*} [Field K] [CharZero K] {s m q r:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b w:Vec K (s+1)} {U:Submodule K (Vec K (s+1))}
noncomputable section

omit [CharZero K] in
/-- Every post-midpoint orbit vector is still a true pure at its budget,
even though not every true pure need be a member of that orbit. -/
theorem orbit_pure (h:MidpointHead A m U w r) (hm:5≤m) (q:ℕ) (low:5≤q) :
    chain (diag (nodes A)) U w (r+(q-5))≤zeroSpace A q := by
  induction q,low using Nat.le_induction with
  | base => rw [←h.band 5 le_rfl hm]
  | succ j hj ih =>
    rw [show r+((j+1)-5)=(r+(j-5))+1 by omega,←chain_sup_map h.invariant (by have:=h.positive;omega)]
    apply sup_le (ih.trans (zeroSpace_mono A (by omega)))
    exact (Submodule.map_mono ih).trans (Submodule.map_le_iff_le_comap.mpr (diag_zeroSpace A j))

omit [CharZero K] in
theorem head_paid (h:MidpointHead A m U w r) (hm:5≤m) : w∈zeroSpace A 5 := by
  rw [h.band 5 le_rfl hm]
  have h0 := ((chain_le_iff (T:=diag (nodes A)) (U:=U) (w:=w) (r+(5-5))).mp le_rfl).2 0
    (by have:=h.positive;omega)
  simpa using h0

/-- Extract the actual scalar, and not only an E_q decomposition: all of its
paid moments vanish, and the two zero coordinates give both endpoints. -/
theorem pure_decompose (h:MidpointHead A m U w r) (hm:m=7 ∨ m=8)
    (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b (2*m)) (he:s+1+3=3*m)
    (low:m≤q) (high:q+3≤2*m) {v:Vec K (s+1)} (hv:v∈zeroSpace A q)
    (vclean:∀i, (∀f∈zeroSpace A 5,f i=0) → v i=0) :
    ∃H:K[X],∃x∈chain (diag (nodes A)) U w (r+(q-5)),
      LobattoPaidTail m (2*m-q-1) H ∧ v=evalNodes A H+x := by
  classical
  let fix : m=7 ∨ m=8 ∨ m=9 ∨ m=10 := hm.imp_right Or.inl
  have seven : 7≤m:=by rcases hm with rfl|rfl <;>decide
  have vt: v∈treeSpace A q := zeroSpace_le_treeSpace A q hv
  rw [h.tree_band fix ha ho he low high] at vt
  obtain ⟨y,⟨a,rfl⟩,x,hx,eqn⟩:=Submodule.mem_sup.mp vt
  let H:=ofFn (m+1) a
  have deg:H.natDegree≤m:=Nat.le_of_lt_succ (ofFn_natDegree_lt (by omega) a)
  have rep:v=evalNodes A H+x:=by rw [show H=ofFn (m+1) a from rfl,evalNodes_ofFn];exact eqn.symm
  have purex:=h.orbit_pure (by omega) q (by omega) hx
  have pureH:evalNodes A H∈zeroSpace A q:=by
    rw [show evalNodes A H=v-x from by rw [rep];abel];exact (zeroSpace A q).sub_mem hv purex
  have disappear (i:Fin (s+1)) (hi:∀f∈zeroSpace A 5,f i=0): H.eval (nodes A i)=0:= by
    obtain ⟨u,hu,Q,_,eq⟩:=Clock.exists_head_poly hx
    have x0:x i=0:=by rw [eq i,hi u (h.paid hu),hi w (h.head_paid (by omega)),mul_zero,add_zero]
    have e:=congrFun rep i
    rw [Pi.add_apply,evalNodes_apply,x0,add_zero,vclean i hi] at e
    exact e.symm
  obtain ⟨origin,_,_,_,_,_,t,_,nt,_,_,terminal⟩:=even_boundary seven ha ho he
  have s0:=disappear 0 (fun _ hh=>zeroSpace_first_of_row origin 5 hh)
  have s1:=disappear t (fun _ hh=>terminal _ (zeroSpace_mono A (by omega) hh))
  rw [show nodes A 0=0 by simp [nodes,origin]] at s0
  rw [nt] at s1
  refine ⟨H,x,hx,⟨deg,s0,s1,?_⟩,rep⟩
  intro k hk
  have zero:=probe_zeroSpace ho (by omega:k+q+1≤2*m) pureH
  have eval:=(OrdinaryTrace.scalar A deg).probe ho k (by omega)
  change probe A b k (evalNodes A H)=0 at zero
  rw [eval,formalPrimitive_eq_treePrimitive] at zero
  exact zero

end
end RKCert.Paired.Terminal.MidpointHead

