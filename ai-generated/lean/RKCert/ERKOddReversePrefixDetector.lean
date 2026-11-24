module
public import RKCert.HeadChart
public import RKCert.DirkMarkedBudget

@[expose] public section
/-! # A true reverse-prefix detector on one simultaneous numerical block
This result uses the original ordered indices, and keeps the cyclic base
arbitrary. It is independent of sign constraints, RK order and numeric
sorting of the two coordinate functions. -/
namespace RKCert.Paired.ReverseHull
open RKCert.Paired.Clock
open scoped Classical
variable {K:Type*} [Field K] {s:ℕ}
noncomputable section

private def reverseSelector (c f:Vec K (s+1))(i:Fin (s+1)) :
    Vec K (s+1)→ₗ[K]Vec K (s+1):=by
  classical
  exact LinearMap.pi (fun k=>if i≤k ∧ c k=c i ∧ f k=f i then LinearMap.proj k else 0)

private theorem reverseSelector_apply (c f:Vec K (s+1))(i:Fin (s+1))(v:Vec K (s+1))(k:Fin (s+1)) :
    reverseSelector c f i v k=if i≤k ∧ c k=c i ∧ f k=f i then v k else 0:=by
  classical
  rw [reverseSelector,LinearMap.pi_apply]
  split <;> rfl

private theorem reverseSelector_adjoint (c f:Vec K (s+1))(i:Fin (s+1))(u v:Vec K (s+1)) :
    row (reverseSelector c f i u) v=row u (reverseSelector c f i v):=by
  classical
  simp only [row_apply,reverseSelector_apply]
  apply Finset.sum_congr rfl
  intro k _
  split <;> simp

structure ReversePrefixDetector
    (c f x:Vec K (s+1))(U:Submodule K (Vec K (s+1)))(i:Fin (s+1))
    (l u:Vec K (s+1)):Prop where
  detects:row l x≠0
  kills:l∈annih U
  previous:u∈U
  matchEarlier:∀k,i<k→x k=u k
  allowed:∀k,l k≠0→i≤k ∧ c k=c i ∧ f k=f i

set_option maxHeartbeats 2200000 in
theorem reverse_prefix_detector {c f x:Vec K (s+1)}{U:Submodule K (Vec K (s+1))}
    (clock:U.map (diag c)≤U)(other:U.map (diag f)≤U)(outside:x∉U) :
    ∃i,∃ℓ u,ReversePrefixDetector c f x U i ℓ u:=by
  classical
  let matched(i:Fin (s+1)):Prop:=∃u∈U,∀k,i≤k→x k=u k
  let bad:Finset (Fin (s+1)):=Finset.univ.filter (fun i=>¬matched i)
  have bz:¬matched 0:=by
    rintro ⟨u,hu,h⟩
    apply outside
    have e:x=u:=funext (fun k=>h k (Fin.zero_le _))
    exact e.symm ▸ hu
  have bn:bad.Nonempty:=⟨0,Finset.mem_filter.mpr ⟨Finset.mem_univ _,bz⟩⟩
  let i:=bad.max' bn
  have bi:¬matched i:=(Finset.mem_filter.mp (bad.max'_mem bn)).2
  have prev:∃u∈U,∀k,i<k→x k=u k:=by
    by_cases last:i=Fin.last s
    · exact ⟨0,U.zero_mem,fun k h=>False.elim (not_lt_of_ge (Fin.le_last k) (by rwa [←last]))⟩
    have lim:i.val<s:=by
      have ei:i.val≤s:=by have h:=i.isLt;omega
      by_contra! e
      exact last (Fin.ext (by rw [Fin.val_last];omega))
    let j:Fin (s+1):=⟨i.val+1,by omega⟩
    have ij:i<j:=by change i.val < i.val + 1;omega
    have good:matched j:=by
      by_contra n
      exact (not_le_of_gt ij) (bad.le_max' _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,n⟩))
    obtain ⟨u,hu,h⟩:=good
    exact ⟨u,hu,fun k hk=>h k (show j.val≤k.val from hk)⟩
  obtain ⟨u₀,up,agree⟩:=prev
  let L:=reverseSelector c f i
  let M(v:Vec K (s+1)):=fiber c (c i) (fiber f (f i) v)
  have M_U(v:Vec K (s+1))(h:v∈U):M v∈U:=fiber_mem clock _ (fiber_mem other _ h)
  have M_eval (v:Vec K (s+1))(k:Fin (s+1)):
      M v k=if c k=c i ∧ f k=f i then v k else 0:=by
    by_cases ec:c k=c i <;> by_cases ef:f k=f i <;> simp [M,fiber,ec,ef]
  have miss:L x∉U.map L:=by
    intro yy
    obtain ⟨v,hv,eq⟩:=yy
    apply bi
    refine ⟨u₀-M u₀+M v,U.add_mem (U.sub_mem up (M_U u₀ up)) (M_U v hv),?_⟩
    intro k ki
    by_cases hk:c k=c i ∧ f k=f i
    · have h:=congrFun eq k
      change reverseSelector c f i v k=reverseSelector c f i x k at h
      have yes:i≤k ∧ c k=c i ∧ f k=f i:=⟨ki,hk⟩
      simp only [reverseSelector_apply,ite_eq_left yes] at h
      have a:M u₀ k=u₀ k:=by rw [M_eval,ite_eq_left hk]
      have b:M v k=v k:=by rw [M_eval,ite_eq_left hk]
      rw [Pi.add_apply,Pi.sub_apply,a,b,sub_self,zero_add]
      exact h.symm
    · have strict:i<k:=lt_of_le_of_ne ki (fun e=>hk (by rw [←e];exact ⟨rfl,rfl⟩))
      simp only [Pi.add_apply,Pi.sub_apply,M_eval,hk,ite_false,sub_zero,add_zero]
      exact agree k strict
  have sep:∃z∈annih (U.map L),row z (L x)≠0:=by
    by_contra! h
    apply miss
    rw [←annih_annih_paired (U.map L)]
    apply mem_annih.mpr
    intro v hv
    have e:row (L x) v=row v (L x):=by simp only [row_apply,mul_comm]
    rw [e]
    exact h v hv
  obtain ⟨z,hz,dz⟩:=sep
  let ℓ:=L z
  refine ⟨i,ℓ,u₀,⟨?_,?_,up,agree,?_⟩⟩
  · exact (reverseSelector_adjoint c f i z x).symm ▸ dz
  · apply mem_annih.mpr
    intro v hv
    rw [show row ℓ v=row z (L v) from reverseSelector_adjoint _ _ _ _ _]
    exact mem_annih.mp hz _ (Submodule.mem_map_of_mem hv)
  · intro k hk
    by_contra e
    apply hk
    change reverseSelector c f i z k=0
    rw [reverseSelector_apply,ite_eq_right e]

end
end RKCert.Paired.ReverseHull

