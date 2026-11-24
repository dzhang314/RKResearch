module
public import RKCert.ERKOddLocalHeadTrace
public import RKCert.ERKOddSignedRows
public import RKCert.ERKOddReverseCore

@[expose] public section
/-! # Complete macroblock census using original stage labels
No compression of the tableaux is used. Distinct clock classes of the
forward masks, true τ support, and true contrast support are separately
counted even when those classes share a numerical abscissa. -/
namespace RKCert.Paired.ReverseHull
open RKCert.Paired.Clock RKCert.Paired.ERKEvenHidden RKCert.Paired.FiniteMidpoint RKCert.Endpoint
open Polynomial Module
open scoped Classical
variable {K:Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A:Fin 26→Fin 26→K}{b τ h z W:Vec K 26}{r:ℕ}{U:Submodule K (Vec K 26)}{Q:K[X]}
noncomputable section

abbrev maskTag (b τ:Vec K 26)(U:Submodule K (Vec K 26)):Type _:=K×K×K×(reverseHidden b τ U→K)
def localMacroTag (A:Fin 26→Fin 26→K)(b τ h:Vec K 26)(U:Submodule K (Vec K 26)):
    Fin 26→maskTag b τ U:=taggedPhysicalBlock (reverseHidden b τ U) (mirror A) h 0

structure LocalMacroAudit (A:Fin 26→Fin 26→K)(b τ h W:Vec K 26)
    (U:Submodule K (Vec K 26))(Q:K[X]):Prop where
  baseZero:U≤(blockTotal (localMacroTag A b τ h U)).ker
  lower:finrank K (reverseHidden b τ U)+(headSites (mirror A) τ).card+
    (headSites (mirror A) W).card≤(physicalBlocks (localMacroTag A b τ h U)).card
  cover:(physicalBlocks (localMacroTag A b τ h U)).card≤
    finrank K (reverseHidden b τ U)+(headSites (mirror A) τ).card+(headSites (mirror A) W).card →
    ∀i:Fin 26,Clock.Live (reverseHidden b τ U) i∨h i=Q.eval (mirror A i)∨
      (h i=0∧Q.eval (mirror A i)≠0∧¬Clock.Live (reverseHidden b τ U) i∧
        mirror A i∈headSites (mirror A) W)

set_option maxHeartbeats 4100000 in
theorem LocalLinearBand.local_macro_audit (B:LocalLinearBand A b r U τ)
    (ho:HasTreeOrderAtLeast A b 17)(T:LocalHeadContrast A b τ h W U Q):
    LocalMacroAudit A b τ h W U Q:=by
  classical
  let : DecidableEq K:=Classical.decEq K
  let y:=mirror A
  let G:=reverseHidden b τ U
  let C:=localMacroTag A b τ h U
  let L:Finset (maskTag b τ U):=physicalBlocks C
  let F:Finset (Fin 26):=Finset.univ.filter (fun i=>Clock.Live G i)
  let A₀:=F.image C
  let μ(a:K):maskTag b τ U:=(a,Q.eval a,0,0)
  let ν(a:K):maskTag b τ U:=(a,0,0,0)
  let A₁:=(headSites y τ).image μ
  let A₂:=(headSites y W).image ν
  have k₀:finrank K G≤A₀.card:=by
    have t:=forward_value_classes_rank G
    have h:A₀.image (fun a:maskTag b τ U=>a.2.2.2)=F.image (forwardValueTag G):=by
      dsimp only [A₀]
      rw [Finset.image_image]
      rfl
    rw [←h] at t
    exact t.trans Finset.card_image_le
  have c₁:A₁.card=(headSites y τ).card:=Finset.card_image_of_injective _ (fun a b h=>congrArg Prod.fst h)
  have c₂:A₂.card=(headSites y W).card:=Finset.card_image_of_injective _ (fun a b h=>congrArg Prod.fst h)
  have ne₀(a:maskTag b τ U)(ha:a∈A₀):a.2.2.2≠0:=by
    obtain ⟨i,ig,rfl⟩:=Finset.mem_image.mp ha
    exact fun z=>(forwardValueTag_zero.mp z) ((Finset.mem_filter.mp ig).2)
  have d₀₁:Disjoint A₀ A₁:=Finset.disjoint_left.mpr (fun a am h=>by
    obtain ⟨x,_,rfl⟩:=Finset.mem_image.mp h
    exact ne₀ _ am rfl)
  have d₀₂:Disjoint A₀ A₂:=Finset.disjoint_left.mpr (fun a am h=>by
    obtain ⟨x,_,rfl⟩:=Finset.mem_image.mp h
    exact ne₀ _ am rfl)
  have wsite(a:K)(ha:a∈headSites y W):Q.eval a≠0:=by
    obtain ⟨i,hw,rfl⟩:=Finset.mem_image.mp ha
    exact (T.contrastValue i (Finset.mem_filter.mp hw).2).2.1
  have d₁₂:Disjoint A₁ A₂:=Finset.disjoint_left.mpr (fun a am h=>by
    obtain ⟨t,ht,te⟩:=Finset.mem_image.mp am
    obtain ⟨v,hv,ve⟩:=Finset.mem_image.mp h
    have e:=te.trans ve.symm
    have eq:t=v:=congrArg Prod.fst e
    have nz:Q.eval t=0:=congrArg (fun a:maskTag b τ U=>a.2.1) e
    exact wsite v hv (eq ▸ nz))
  have Hshape(i:Fin 26)(ti:τ i≠0):C i=μ (y i):=by
    have q:=T.headValue i ti
    change (y i,h i,0,forwardValueTag G i)=(y i,Q.eval (y i),0,0)
    rw [q.1,forwardValueTag_zero.mpr q.2]
  have Wshape(i:Fin 26)(wi:W i≠0):C i=ν (y i):=by
    have q:=T.contrastValue i wi
    change (y i,h i,0,forwardValueTag G i)=(y i,0,0,0)
    rw [q.1,forwardValueTag_zero.mpr q.2.2]
  have incl:A₀∪A₁∪A₂⊆L:=by
    intro a ha
    rcases Finset.mem_union.mp ha with a01|a2
    · rcases Finset.mem_union.mp a01 with a0|a1
      · obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp a0
        exact site_block_mem C i
      · obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp a1
        obtain ⟨i,hh,rfl⟩:=Finset.mem_image.mp hx
        rw [←Hshape i (Finset.mem_filter.mp hh).2]
        exact site_block_mem C i
    · obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp a2
      obtain ⟨i,hh,rfl⟩:=Finset.mem_image.mp hx
      rw [←Wshape i (Finset.mem_filter.mp hh).2]
      exact site_block_mem C i
  have cc:(A₀∪A₁∪A₂).card=A₀.card+(headSites y τ).card+(headSites y W).card:=by
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨d₀₂,d₁₂⟩),
      Finset.card_union_of_disjoint d₀₁,c₁,c₂]
  have lo:finrank K G+(headSites y τ).card+(headSites y W).card≤L.card:=by
    have h:=Finset.card_le_card incl
    omega
  refine ⟨?_,lo,?_⟩
  · have hi:U.map (diag h)≤U:=by rintro _ ⟨v,hv,rfl⟩;exact T.preserved v hv
    have ij:U.map (diag (0:Vec K 26))≤U:=by
      rintro _ ⟨v,_,rfl⟩
      have z:diag (0:Vec K 26) v=0:=by ext i;simp [diag_apply]
      rw [z];exact U.zero_mem
    exact tagged_blocks_zero_on_base reverse_hidden_mul (fun g hg v hv=>(mem_reverseHidden.mp hg).2.2 v hv)
          B.clock hi ij (fun v hv=>by
            have m:=mem_annih.mp (B.base_annih ho hv) (1:Vec K 26)
              (stageWeight_mem_space A .leaf (by change 1≤16-r+1;omega))
            simpa only [row_apply,Pi.one_apply,mul_one] using m)
  · intro up i
    have e:L=A₀∪A₁∪A₂:=by
      symm
      apply Finset.eq_of_subset_of_card_le incl
      change L.card≤_ at up
      have n:finrank K G+(headSites y τ).card+(headSites y W).card≥L.card:=up
      omega
    have hi:=site_block_mem C i
    change C i∈L at hi
    rw [e] at hi
    rcases Finset.mem_union.mp hi with ca|cw
    · rcases Finset.mem_union.mp ca with cg|ct
      · exact Or.inl (by
          by_contra no
          exact ne₀ _ cg (forwardValueTag_zero.mpr no))
      · right;left
        obtain ⟨a,ha,ah⟩:=Finset.mem_image.mp ct
        have eq:a=y i:=congrArg Prod.fst ah
        have hq:Q.eval a=h i:=congrArg (fun a:maskTag b τ U=>a.2.1) ah
        rw [eq] at hq
        exact hq.symm
    · right;right
      obtain ⟨a,ha,e⟩:=Finset.mem_image.mp cw
      have eq:a=y i:=congrArg Prod.fst e
      have q:h i=0:=(congrArg (fun a:maskTag b τ U=>a.2.1) e).symm
      have z:forwardValueTag G i=0:=(congrArg (fun a:maskTag b τ U=>a.2.2.2) e).symm
      refine ⟨q,?_,forwardValueTag_zero.mp z,?_⟩
      · change Q.eval (y i)≠0
        rw [←eq]
        exact wsite a ha
      · change y i∈headSites y W
        rwa [←eq]
end
end RKCert.Paired.ReverseHull

