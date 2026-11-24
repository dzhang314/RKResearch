module
public import RKCert.DirkMidpointCoreProduct
public import RKCert.DirkShiftedHeadMask
@[expose] public section
namespace RKCert.Paired.Terminal.MidpointHead
open Polynomial Module RKCert.OneEscape RKCert.Endpoint
variable {K:Type*} [Field K] [CharZero K] {s m r:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b w:Vec K (s+1)} {U:Submodule K (Vec K (s+1))}
noncomputable section

/-- The same genuine terminal as the clean endpoint of the forward band
supplies an exact scalar/head equation on every physically unmasked row. -/
theorem head_cardinal (h:MidpointHead A m U w r) (hm:m=7 ∨ m=8)
    (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b (2*m)) (he:s+1+3=3*m)
    (sep:∀i,Clock.Live U i → w i=0) :
    ∃β:K,∃Q:K[X], β≠0 ∧ Q.natDegree<r+(m-5) ∧
      ∀i,w i≠0 → β*(lobatto m).eval (nodes A i)+Q.eval (nodes A i)*w i=0 :=by
  classical
  let fix : m=7 ∨ m=8 ∨ m=9 ∨ m=10 := hm.imp_right Or.inl
  have seven:7≤m:=by rcases hm with rfl|rfl <;>decide
  obtain ⟨origin,_,_,_,_,_,t,bt,ct,card,_,endclean⟩:=even_boundary seven ha ho he
  have ⟨mom,atOne⟩:=lobatto_fixed (K:=K) fix
  have c0:nodes A 0=0:=by simp [nodes,origin]
  obtain ⟨cardG,_,_⟩:=lobatto_tableau ho (by omega) (by omega) 0 t c0 ct
    (fun f hf=>zeroSpace_first_of_row origin m hf) endclean card mom atOne
  rw [h.band m (by omega) le_rfl] at cardG
  obtain ⟨u,hu,Q,dQ,rep⟩:=Clock.exists_head_poly cardG
  have rn:0<r+(m-5):=by have:=h.positive;omega
  have deg:Q.natDegree<r+(m-5):=by
    by_cases z:Q=0
    · simp [z,rn]
    · exact (natDegree_lt_iff_degree_lt z).mpr dQ
  refine ⟨b t,Q,bt,deg,?_⟩
  intro i wi
  have wt:w t=0:=endclean w (zeroSpace_mono A (by omega) (h.head_paid (by omega)))
  have it:i≠t:=fun z=>wi (z ▸ wt)
  have uz:u i=0:=by by_contra nz;exact wi (sep i ⟨u,hu,nz⟩)
  have e:=rep i
  simp only [Pi.sub_apply,Pi.single_eq_of_ne it,Pi.smul_apply,smul_eq_mul,evalNodes_apply,uz,zero_add,zero_sub] at e
  linear_combination -e

/-- If two actual consecutive clock powers have grade-ten decompositions,
their scalar parts differ, modulo the fixed grid, by multiplication by X. -/
theorem link_products (h:MidpointHead A m U w r) (hm:m=7 ∨ m=8)
    (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b (2*m)) (he:s+1+3=3*m)
    {H J:K[X]} (dH:H.natDegree≤m) (dJ:J.natDegree≤m) {x y v:Vec K (s+1)}
    (hx:x∈chain (diag (nodes A)) U w (r+(10-5))) (hy:y∈chain (diag (nodes A)) U w (r+(10-5)))
    (first:v=evalNodes A H+x) (next:diag (nodes A) v=evalNodes A J+y) :
    (X-1)*lobatto m ∣ X*H-J :=by
  have up:m≤8:=by rcases hm with rfl|rfl <;>decide
  have low:7≤m:=by rcases hm with rfl|rfl <;>decide
  have shift:diag (nodes A) x∈chain (diag (nodes A)) U w (r+(11-5)):=by
    rw [show r+(11-5)=(r+(10-5))+1 by omega,←chain_sup_map h.invariant (by have:=h.positive;omega)]
    exact (le_sup_right : (chain (diag (nodes A)) U w (r+(10-5))).map (diag (nodes A))≤ _) ⟨_,hx,rfl⟩
  have num:evalNodes A (X*H-J)=y-diag (nodes A) x :=by
    rw [first,map_add] at next
    ext i
    have e:=congrFun next i
    simp only [evalNodes_apply,eval_sub,eval_mul,eval_X,Pi.sub_apply,diag_apply,Pi.add_apply] at e ⊢
    linear_combination e
  apply h.grid_dvd_of_pure_polynomial (hm.imp_right Or.inl) ha ho he (q:=11) (by omega) (by omega)
  · exact (natDegree_sub_le _ _).trans (max_le (natDegree_mul_le.trans (by rw [natDegree_X];omega)) (by omega))
  · rw [num];exact (chain _ _ _ _).sub_mem ((chain_length_le (by omega:r+(10-5)≤r+(11-5))) hy) shift

end
end RKCert.Paired.Terminal.MidpointHead

