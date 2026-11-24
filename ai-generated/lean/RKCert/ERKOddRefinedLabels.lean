module
public import RKCert.ERKOddLabelGain
public import RKCert.ERKOddRefinedContrast

@[expose] public section
/-! # Refined census: actual two features, with a genuine split clock -/
namespace RKCert.Paired.ReverseHull
open RKCert.Paired.Clock RKCert.Paired.ERKEvenHidden RKCert.Paired.FiniteMidpoint RKCert.Endpoint Polynomial Module
open scoped Classical
variable {K:Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A:Fin 26→Fin 26→K}{b τ h ξ W:Vec K 26}{U:Submodule K (Vec K 26)}{Q:K[X]}
noncomputable section

structure RefinedMacroAudit (A:Fin 26→Fin 26→K)(b τ h ξ W:Vec K 26)
    (U:Submodule K (Vec K 26))(Q:K[X]):Prop where
  baseZero:U≤(blockTotal (localRefinedTag A b τ h ξ U)).ker
  lower:finrank K (reverseHidden b τ U)+(refinedHeadBlocks A b τ h ξ U).card+
    (headSites (mirror A) W).card≤(physicalBlocks (localRefinedTag A b τ h ξ U)).card
  cover:(physicalBlocks (localRefinedTag A b τ h ξ U)).card≤
    finrank K (reverseHidden b τ U)+(refinedHeadBlocks A b τ h ξ U).card+(headSites (mirror A) W).card →
    ∀i:Fin 26,¬Clock.Live (reverseHidden b τ U) i→h i≠Q.eval (mirror A i)→
      h i=0∧ξ i=0∧mirror A i∈headSites (mirror A) W

set_option maxHeartbeats 5600000 in
theorem LocalLinearBand.refined_macro_audit (B:LocalLinearBand A b 2 U τ)
    (ho:HasTreeOrderAtLeast A b 17)(D:LocalFourAxis A b τ h ξ U)
    (T:LocalHeadContrast A b τ h W U Q)(xzero:∀i,W i≠0→ξ i=0):
    RefinedMacroAudit A b τ h ξ W U Q:=by
  classical
  let : DecidableEq K:=Classical.decEq K
  let y:=mirror A
  let G:=reverseHidden b τ U
  let C:=localRefinedTag A b τ h ξ U
  let L:Finset (maskTag b τ U):=physicalBlocks C
  let F:Finset (Fin 26):=Finset.univ.filter (fun i=>Clock.Live G i)
  let A₀:=F.image C
  let A₁:=refinedHeadBlocks A b τ h ξ U
  let ν(a:K):maskTag b τ U:=(a,0,0,0)
  let A₂:=(headSites y W).image ν
  have k₀:finrank K G≤A₀.card:=by
    have t:=forward_value_classes_rank G
    have h:A₀.image (fun a:maskTag b τ U=>a.2.2.2)=F.image (forwardValueTag G):=by
      dsimp only [A₀]
      rw [Finset.image_image]
      rfl
    rw [←h] at t
    exact t.trans Finset.card_image_le
  have c₂:A₂.card=(headSites y W).card:=Finset.card_image_of_injective _ (fun a b h=>congrArg Prod.fst h)
  have ne₀(a:maskTag b τ U)(ha:a∈A₀):a.2.2.2≠0:=by
    obtain ⟨i,ig,rfl⟩:=Finset.mem_image.mp ha
    exact fun z=>(forwardValueTag_zero.mp z) ((Finset.mem_filter.mp ig).2)
  have Wnz(a:K)(ha:a∈headSites y W):Q.eval a≠0:=by
    obtain ⟨i,hw,rfl⟩:=Finset.mem_image.mp ha
    exact (T.contrastValue i (Finset.mem_filter.mp hw).2).2.1
  have headTag (i:Fin 26)(ti:τ i≠0):C i=(y i,Q.eval (y i),ξ i,0):=by
    have q:=T.headValue i ti
    change (y i,h i,ξ i,forwardValueTag G i)=(y i,Q.eval (y i),ξ i,0)
    rw [q.1,forwardValueTag_zero.mpr q.2]
  have d₀₁:Disjoint A₀ A₁:=Finset.disjoint_left.mpr (fun l lm hx=>by
    obtain ⟨i,hi,rfl⟩:=refined_head_block_mem.mp hx
    exact ne₀ _ lm (congrArg (fun a:maskTag b τ U=>a.2.2.2) (headTag i ((mem_activeRows i).mp hi))))
  have d₀₂:Disjoint A₀ A₂:=Finset.disjoint_left.mpr (fun l lm hx=>by
    obtain ⟨x,_,rfl⟩:=Finset.mem_image.mp hx
    exact ne₀ _ lm rfl)
  have d₁₂:Disjoint A₁ A₂:=Finset.disjoint_left.mpr (fun l lm hx=>by
    obtain ⟨i,hi,te⟩:=refined_head_block_mem.mp lm
    obtain ⟨v,hv,ve⟩:=Finset.mem_image.mp hx
    have e:((y i,Q.eval (y i),ξ i,0):maskTag b τ U)=ν v:=
      (headTag i ((mem_activeRows i).mp hi)).symm.trans (te.trans ve.symm)
    have eq:y i=v:=congrArg Prod.fst e
    have nz:Q.eval (y i)=0:=congrArg (fun a:maskTag b τ U=>a.2.1) e
    exact Wnz v hv (eq ▸ nz))
  have Wshape(i:Fin 26)(wi:W i≠0):C i=ν (y i):=by
    have q:=T.contrastValue i wi
    change (y i,h i,ξ i,forwardValueTag G i)=(y i,0,0,0)
    rw [q.1,xzero i wi,forwardValueTag_zero.mpr q.2.2]
  have incl:A₀∪A₁∪A₂⊆L:=by
    intro a ha
    rcases Finset.mem_union.mp ha with a01|a2
    · rcases Finset.mem_union.mp a01 with a0|a1
      · obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp a0
        exact site_block_mem C i
      · obtain ⟨i,_,rfl⟩:=refined_head_block_mem.mp a1
        exact site_block_mem C i
    · obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp a2
      obtain ⟨i,hh,rfl⟩:=Finset.mem_image.mp hx
      rw [←Wshape i (Finset.mem_filter.mp hh).2]
      exact site_block_mem C i
  have cc:(A₀∪A₁∪A₂).card=A₀.card+A₁.card+(headSites y W).card:=by
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨d₀₂,d₁₂⟩),
      Finset.card_union_of_disjoint d₀₁,c₂]
  have lo:finrank K G+A₁.card+(headSites y W).card≤L.card:=by
    have h:=Finset.card_le_card incl
    omega
  refine ⟨?_,lo,?_⟩
  · have hi:U.map (diag h)≤U:=by rintro _ ⟨v,hv,rfl⟩;exact T.preserved v hv
    have xi:U.map (diag ξ)≤U:=by rintro _ ⟨v,hv,rfl⟩;exact B.mul_base ho (by decide) D.sixth hv
    exact tagged_blocks_zero_on_base reverse_hidden_mul (fun g hg v hv=>(mem_reverseHidden.mp hg).2.2 v hv)
      B.clock hi xi (fun v hv=>by
        have m:=mem_annih.mp (B.base_annih ho hv) (1:Vec K 26)
          (stageWeight_mem_space A .leaf (by decide))
        simpa only [row_apply,Pi.one_apply,mul_one] using m)
  · intro up i dead bad
    have e:L=A₀∪A₁∪A₂:=by
      symm
      apply Finset.eq_of_subset_of_card_le incl
      change L.card≤finrank K G+A₁.card+(headSites y W).card at up
      omega
    have hi:=site_block_mem C i
    change C i∈L at hi
    rw [e] at hi
    rcases Finset.mem_union.mp hi with ca|cw
    · rcases Finset.mem_union.mp ca with cg|ct
      · exact False.elim (ne₀ _ cg (forwardValueTag_zero.mpr dead))
      · obtain ⟨j,hj,je⟩:=refined_head_block_mem.mp ct
        have z:((y j,Q.eval (y j),ξ j,0):maskTag b τ U)=C i:=
          (headTag j ((mem_activeRows j).mp hj)).symm.trans je
        have eq:y j=y i:=congrArg Prod.fst z
        have hq:Q.eval (y j)=h i:=congrArg (fun a:maskTag b τ U=>a.2.1) z
        rw [eq] at hq
        exact False.elim (bad hq.symm)
    · obtain ⟨a,ha,e⟩:=Finset.mem_image.mp cw
      have eq:a=y i:=congrArg Prod.fst e
      have q:h i=0:=(congrArg (fun a:maskTag b τ U=>a.2.1) e).symm
      have x:ξ i=0:=(congrArg (fun a:maskTag b τ U=>a.2.2.1) e).symm
      refine ⟨q,x,?_⟩
      change y i∈headSites y W
      rwa [←eq]
end
end RKCert.Paired.ReverseHull
