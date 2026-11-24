module
public import RKCert.ERKOddLocalLow

@[expose] public section
/-! # One invariant extra ordinary dimension is a localized clock eigenline -/
namespace RKCert.Paired.ReverseHull
open RKCert.Paired.Clock RKCert.Paired.FiniteMidpoint RKCert.Endpoint Polynomial Module
variable {K:Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
noncomputable section

theorem nested_dot_complement {s:ℕ}{U V:Submodule K (Vec K s)}(inc:U≤V):
    V=U⊔(V⊓annih U):=by
  apply le_antisymm ?_ (sup_le inc inf_le_left)
  intro v vv
  have h:v∈U⊔annih U:=by rw [dot_split_own_annih];exact Submodule.mem_top
  obtain ⟨u,uu,w,wo,eq⟩:=Submodule.mem_sup.mp h
  have wV:w∈V:=by
    have e:w=v-u:=by rw [←eq];abel
    rw [e]
    exact V.sub_mem vv (inc uu)
  exact Submodule.mem_sup.mpr ⟨u,uu,w,⟨wV,wo⟩,eq⟩

theorem extra_invariant_one_fiber {s:ℕ}{y τ:Vec K s}{M V:Submodule K (Vec K s)}
    (inc:M≤V)(dim:finrank K V=finrank K M+1)
    (Mi:M.map (diag y)≤M)(Vi:V.map (diag y)≤V)
    (kill:∀v∈M,τ*v=0):
    ∃a:K,∀v∈V,∀i,y i≠a→τ i*v i=0:=by
  let T:=V⊓annih M
  have e:V=M⊔T:=nested_dot_complement inc
  have iT:M⊓T=⊥:=by
    apply le_bot_iff.mp
    rintro v ⟨u,vv⟩
    exact dot_orthogonal_inter_zero u vv.2
  have d:finrank K T=1:=by
    have h:=Submodule.finrank_sup_add_finrank_inf_eq M T
    rw [←e,iT,finrank_bot,add_zero,dim] at h
    omega
  have inv:T.map (diag y)≤T:=by
    rintro _ ⟨v,hv,rfl⟩
    exact ⟨Vi (Submodule.mem_map_of_mem hv.1),
      diag_annih_invariant Mi (Submodule.mem_map_of_mem hv.2)⟩
  obtain ⟨ξ,ξT,nz⟩:∃v∈T,v≠0:=by
    by_contra! none
    have z:T=⊥:=le_bot_iff.mp (fun v h=>none v h)
    rw [z,finrank_bot] at d
    omega
  have axes:K∙ξ=T:=by
    apply Submodule.eq_of_le_of_finrank_le ((Submodule.span_singleton_le_iff_mem ..).mpr ξT)
    rw [d,finrank_span_singleton nz]
  have p:diag y ξ∈K∙ξ:=axes.symm ▸ inv (Submodule.mem_map_of_mem ξT)
  obtain ⟨a,ae⟩:=Submodule.mem_span_singleton.mp p
  have ξ0 (i:Fin s)(ne:y i≠a):ξ i=0:=by
    have h:=congrFun ae i
    change a*ξ i=y i*ξ i at h
    have ee:(y i-a)*ξ i=0:=by linear_combination -h
    exact (mul_eq_zero.mp ee).resolve_left (sub_ne_zero.mpr ne)
  refine ⟨a,fun v vv i ne=>?_⟩
  rw [e,←axes] at vv
  obtain ⟨m,mM,w,wT,eq⟩:=Submodule.mem_sup.mp vv
  obtain ⟨s,rfl⟩:=Submodule.mem_span_singleton.mp wT
  have z:=congrFun (kill m mM) i
  rw [←eq,Pi.add_apply,Pi.smul_apply,ξ0 i ne,smul_zero,add_zero]
  exact z

variable {A:Fin 26→Fin 26→K}{b τ:Vec K 26}{r j:ℕ}{U:Submodule K (Vec K 26)}
theorem LocalLinearBand.single_head_site_hidden (B:LocalLinearBand A b r U τ)
    (ho:HasTreeOrderAtLeast A b 17)(pay:j+r+1≤8)
    {f:Vec K 26}(hf:f∈zeroSpace A j) {a:K}
    (off:∀i,mirror A i≠a→τ i*f i=0):f∈reverseHidden b τ U:=by
  classical
  let : DecidableEq K:=Classical.decEq K
  let y:=mirror A
  let T:=(headSites y τ).erase a
  have bnd:8-r≤T.card:=by
    have h:=Finset.pred_card_le_card_erase (s:=headSites y τ) (a:=a)
    change (headSites y τ).card-1≤T.card at h
    have e:=B.sites
    change 9-r≤(headSites y τ).card at e
    rcases B.short with n|n <;> omega
  obtain ⟨Q,dQ,rep⟩:=B.head_trace ho hf pay
  have Q0:Q=0:=by
    apply eq_of_degrees_lt_of_eval_finset_eq T
    · exact degree_le_natDegree.trans_lt (by exact_mod_cast (show Q.natDegree<T.card by omega))
    · exact degree_le_natDegree.trans_lt (by rw [natDegree_zero];exact_mod_cast (show 0<T.card by omega))
    intro a' h
    obtain ⟨ne,si⟩:=Finset.mem_erase.mp h
    obtain ⟨i,ii,rfl⟩:=Finset.mem_image.mp si
    have h:=congrFun rep i
    rw [weightedEval_apply,Pi.mul_apply,off i ne] at h
    rw [eval_zero]
    exact (mul_eq_zero.mp h).resolve_right (Finset.mem_filter.mp ii).2
  apply B.hidden_of_zero_profile ho (by omega) hf
  rw [←rep,Q0,map_zero]

end
end RKCert.Paired.ReverseHull

