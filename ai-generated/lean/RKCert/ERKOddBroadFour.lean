module
public import RKCert.ERKOddBroadCarrier
public import RKCert.ERKFourHiddenDispatch

@[expose] public section
/-! # Four-hidden exclusion in the full wide linear-seed case -/
namespace RKCert.Paired.ReverseHull
open RKCert.Paired.Clock RKCert.Paired.FiniteMidpoint RKCert.Endpoint Polynomial Module
variable {K:Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A:Fin 26→Fin 26→K}{b:Vec K 26}
noncomputable section

theorem linear_fit_invisible {v:Vec K 26}{Q P:K[X]} (fit:LinearFits A b v Q P)
    (qz:Q=0):∀i,linearVisible A b i→v i=0:=by
  intro i vi
  have q:=fit.1 i
  rw [qz,eval_zero,zero_mul] at q
  rcases vi with hi|hi
  · exact (mul_eq_zero.mp q).resolve_left hi
  by_cases d:backSeed1 A b i=0
  · have e:=fit.2 i
    rw [d,mul_zero] at e
    exact (mul_eq_zero.mp e).resolve_left hi
  · exact (mul_eq_zero.mp q).resolve_left d

set_option maxHeartbeats 3200000 in
theorem BroadLinearCover.no_four_hidden (B:BroadLinearCover A b 8 7)
    (ha:StrictLower A)(ho:HasTreeOrderAtLeast A b 17)(S:OddBalanced (s:=25) A b 8)
    (dim:finrank K (linearCarrier A b)=4):False:=by
  classical
  let : DecidableEq K:=Classical.decEq K
  let y:=mirror A
  let d:=backSeed1 A b
  let H:=linearCarrier A b
  let V:=linearVisible A b
  have hh:H≤zeroSpace A 8:=fun _ h=>B.pure_off_linear ho ((linear_carrier_iff S.lastLive).mp h).2
  have hcl:H.map (diag (nodes A))≤H:=linear_carrier_clock S.lastLive
  have cap:finrank K (zeroSpace A 9)≤11:=by
    have R:=S.nextCap
    change finrank K (zeroSpace A 9)+_≤11 at R
    omega
  have det (v:Vec K 26)(hv:v∈zeroSpace A 8)(h:∀i,V i→v i=0):v∈H:=
    (linear_carrier_iff S.lastLive).mpr ⟨origin_zeroSpace A ha 8 hv,h⟩
  refine four_hidden_rank_dispatch ha ho (by decide) (by decide) S.separated S.forwardMid cap H hh dim hcl V
    (fun _ h=>((linear_carrier_iff S.lastLive).mp h).2) det ?_ ?_
  · rintro f hf ⟨a,sup⟩
    obtain ⟨Q,P,qD,pD,fit⟩:=broad_linear_two_traces ho B hf (by decide) (by decide) (by decide)
    let D:=(headSites y d).erase (1-a)
    have sites:8<(headSites y d).card:=B.sites
    have cd:8≤D.card:=by
      have e:=Finset.pred_card_le_card_erase (s:=headSites y d) (a:=1-a)
      change (headSites y d).card-1≤D.card at e
      omega
    have qz:Q=0:=by
      apply eq_of_degrees_lt_of_eval_finset_eq D
      · exact degree_le_natDegree.trans_lt (by exact_mod_cast (show Q.natDegree<D.card by omega))
      · exact degree_le_natDegree.trans_lt (by rw [natDegree_zero];exact_mod_cast (show 0<D.card by omega))
      intro x hx
      obtain ⟨nx,g⟩:=Finset.mem_erase.mp hx
      obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp g
      have dz:d i≠0:=(Finset.mem_filter.mp hi).2
      have off:nodes A i≠a:=fun z=>nx (by change 1-nodes A i=1-a;rw [z])
      have q:=fit.1 i
      rw [sup i (Or.inl dz) off,mul_zero] at q
      rw [eval_zero]
      exact (mul_eq_zero.mp q.symm).resolve_right dz
    exact det f (zeroSpace_mono A (by decide:6≤8) hf) (linear_fit_invisible fit qz)
  · intro j small w powers
    have j5:5≤j:=by rcases small with e|e <;> omega
    have j6:j≤6:=by rcases small with e|e <;> omega
    have wn:w∈zeroSpace A 8:=by
      have h:=powers 0 (by omega)
      rw [pow_zero,one_apply_eq_self] at h
      exact sup_le (zeroSpace_mono A (by omega:j≤8)) hh h
    let L:K[X]:=1-X
    have lD:L.natDegree=1:=one_sub_X_natDegree
    have lx(i:Fin 26):L.eval (y i)=nodes A i:=by simp [L,y,mirror]
    have trace(a:ℕ)(pay:a≤j-4):∃Q P:K[X],Q.natDegree≤j ∧ P.natDegree≤j-1 ∧
        (weightedEval y d Q=(fun i=>L.eval (y i)^a*(d i*w i)))∧
        (weightedEval y d P=(fun i=>L.eval (y i)^a*(b i*w i))) :=by
      obtain ⟨f,hf,u,hu,eq⟩:=Submodule.mem_sup.mp (powers a (by omega))
      obtain ⟨Q,P,dQ,dP,fit⟩:=broad_linear_two_traces ho B hf (by omega) (by decide) (by omega)
      have fE(i:Fin 26)(vi:V i):f i=nodes A i^a*w i:=by
        have ee:=congrFun eq i
        rw [Pi.add_apply,((linear_carrier_iff S.lastLive).mp hu).2 i vi,add_zero,pow_diag_apply] at ee
        exact ee
      refine ⟨Q,P,dQ,dP,?_,?_⟩
      · ext i
        rw [weightedEval_apply,lx,←show d i*f i=Q.eval (y i)*d i from fit.1 i]
        by_cases z:d i=0
        · simp [z]
        rw [fE i (Or.inl z)]
        ring
      · ext i
        rw [weightedEval_apply,lx,←show b i*f i=P.eval (y i)*d i from fit.2 i]
        by_cases z:b i=0
        · simp [z]
        rw [fE i (Or.inr z)]
        ring
    have big:8<(headSites y d).card:=B.sites
    obtain ⟨Q,qD,eQ⟩:=trace_degree_from_affine_shifts (c:=y) (d:=d) L lD (h:=j) (k:=j-4) (by omega)
      (v:=fun i=>d i*w i) (fun a ha=>by obtain ⟨Q,_,dQ,_,q,_⟩:=trace a ha;exact ⟨Q,dQ,q⟩)
    obtain ⟨P,pD,eP⟩:=trace_degree_from_affine_shifts (c:=y) (d:=d) L lD (h:=j-1) (k:=j-4) (by omega)
      (v:=fun i=>b i*w i) (fun a ha=>by obtain ⟨_,P,_,dP,_,p⟩:=trace a ha;exact ⟨P,dP,p⟩)
    have q4:Q.natDegree≤4:=by
      rcases qD with e|e
      · simp [e]
      · omega
    have p3:P.natDegree≤3:=by
      rcases pD with e|e
      · simp [e]
      · omega
    have fits:LinearFits A b w Q P:=⟨fun i=>by simpa only [weightedEval_apply] using (congrFun eQ i).symm,
      fun i=>by simpa only [weightedEval_apply] using (congrFun eP i).symm⟩
    have zero:=ordered_broad_invisible_given_reps ha ho B Q P q4 (by omega) (by omega) (by omega) (by omega) fits
    apply det w wn
    intro i vi
    rcases vi with v|v
    · exact (mul_eq_zero.mp (zero i).1).resolve_left v
    · exact (mul_eq_zero.mp (zero i).2).resolve_left v

theorem BroadLinearCover.hidden_rank_five (B:BroadLinearCover A b 8 7)
    (ha:StrictLower A)(ho:HasTreeOrderAtLeast A b 17)(S:OddBalanced (s:=25) A b 8):
    finrank K (linearCarrier A b)=5:=by
  let H:=linearCarrier A b
  change finrank K H=5
  have inc:H≤zeroSpace A 8:=fun _ h=>B.pure_off_linear ho ((linear_carrier_iff S.lastLive).mp h).2
  have cap:finrank K (zeroSpace A 9)≤11:=by
    have R:=S.nextCap
    change finrank K (zeroSpace A 9)+_≤11 at R
    omega
  have up:=invariant_core_cap_of_rank ha ho (by decide) (by decide) S.separated S.forwardMid cap H inc
    (linear_carrier_clock S.lastLive)
  have pay:=B.feeder ha ho S.lastLive
  change finrank K (zeroSpace A 3)+2≤finrank K H at pay
  have e:=strict_rank_interval ha S.separated 1 2 (by decide) (by decide)
  change finrank K (zeroSpace A 1)+2≤finrank K (zeroSpace A 3) at e
  by_contra h
  apply B.no_four_hidden ha ho S
  change finrank K H=4
  omega

end
end RKCert.Paired.ReverseHull

