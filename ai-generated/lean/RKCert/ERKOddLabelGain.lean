module
public import RKCert.ERKOddMacroMass
public import RKCert.ERKOddPaidOrbit

@[expose] public section
/-! # At least sixteen labelled physical head blocks for the rank-two slice
At the exceptional fifteen-clock case, an actual nonzero local advance
splits one numerical fiber. Its two different entries are not averaged. -/
namespace RKCert.Paired.ReverseHull
open RKCert.Paired.Clock RKCert.Paired.ERKEvenHidden RKCert.Paired.FiniteMidpoint RKCert.Endpoint Polynomial Module
open scoped Classical
variable {K:Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A:Fin 26→Fin 26→K}{b τ h ξ W ℓ:Vec K 26}{U:Submodule K (Vec K 26)}{Q:K[X]}
noncomputable section

def localRefinedTag (A:Fin 26→Fin 26→K)(b τ h ξ:Vec K 26)(U:Submodule K (Vec K 26)):
    Fin 26→maskTag b τ U:=taggedPhysicalBlock (reverseHidden b τ U) (mirror A) h ξ

def refinedHeadBlocks (A:Fin 26→Fin 26→K)(b τ h ξ:Vec K 26)(U:Submodule K (Vec K 26)):
    Finset (maskTag b τ U):=(activeRows τ).image (localRefinedTag A b τ h ξ U)

omit [IsStrictOrderedRing K] in
theorem refined_head_block_mem {a:maskTag b τ U}:
    a∈refinedHeadBlocks A b τ h ξ U↔
      ∃i∈activeRows τ,localRefinedTag A b τ h ξ U i=a:=by
  classical
  exact Finset.mem_image

omit [IsStrictOrderedRing K] in
theorem refined_head_labels_project (A:Fin 26→Fin 26→K)(b τ h ξ:Vec K 26)(U:Submodule K (Vec K 26)):
    (refinedHeadBlocks A b τ h ξ U).image Prod.fst=headSites (mirror A) τ:=by
  classical
  ext a
  simp [refinedHeadBlocks,Finset.image_image,headSites,localRefinedTag,taggedPhysicalBlock,activeRows]

omit [IsStrictOrderedRing K] in
theorem refined_head_blocks_ge (A:Fin 26→Fin 26→K)(b τ h ξ:Vec K 26)(U:Submodule K (Vec K 26)):
    (headSites (mirror A) τ).card≤(refinedHeadBlocks A b τ h ξ U).card:=by
  rw [←refined_head_labels_project A b τ h ξ U]
  exact Finset.card_image_le

omit [IsStrictOrderedRing K] in
theorem refined_head_blocks_split (i j:Fin 26)(it:τ i≠0)(jt:τ j≠0)
    (x:mirror A i=mirror A j)(e:ξ i≠ξ j):
    (headSites (mirror A) τ).card<(refinedHeadBlocks A b τ h ξ U).card:=by
  let D:=refinedHeadBlocks A b τ h ξ U
  let t:=localRefinedTag A b τ h ξ U
  have iD:t i∈D:=Finset.mem_image_of_mem _ ((mem_activeRows i).mpr it)
  have jD:t j∈D:=Finset.mem_image_of_mem _ ((mem_activeRows j).mpr jt)
  have no:¬Set.InjOn Prod.fst (D:Set (maskTag b τ U)):=by
    intro H
    exact e (congrArg (fun k:maskTag b τ U=>k.2.2.1) (H iD jD x))
  have low:(D.image Prod.fst).card≤D.card:=Finset.card_image_le
  have d:(D.image Prod.fst).card≠D.card:=mt (Finset.card_image_iff.mp) no
  have g:(D.image Prod.fst).card<D.card:=lt_of_le_of_ne low d
  rw [show D=refinedHeadBlocks A b τ h ξ U from rfl,refined_head_labels_project] at g
  exact g

private theorem LocalLinearBand.eight_of_all_clock_masses_zero (B:LocalLinearBand A b 2 U τ)
    (ha:StrictLower A)(ho:HasTreeOrderAtLeast A b 17)(S:OddBalanced (s:=25) A b 8)
    (six:7≤finrank K (zeroSpace A 6))(masks:finrank K (reverseHidden b τ U)=4)
    (T:LocalHeadContrast A b τ h W U Q)
    (zero:∀z∈headSites (mirror A) τ,clockMass (mirror A) τ z=0):
    (headSites (mirror A) τ).card=8:=by
  let y:=mirror A
  let c:=localMacroTag A b τ h U
  let V:=nodalOrbit y τ
  have big:8≤(headSites y τ).card:=B.extra_site_if_six_rich ha ho S six
  have ww:4≤(headSites y W).card:=four_sites_of_unit_contrast _ _ _ T.degree T.nonzero T.moments
  have M:=B.local_macro_audit ho T
  have k:=T.orbit_macro_kernel_of_zero_masses zero
  have vo:V≤annih U:=by
    change nodalOrbit y τ≤_
    rw [nodalOrbit_eq_weightedEval]
    rintro _ ⟨P,rfl⟩
    exact weightedEval_orthogonal B.clock B.orthogonal P
  have pay:=rank_with_physical_blocks c U V M.baseZero k vo
  rw [B.dimension,show finrank K V=(headSites y τ).card from nodalOrbit_rank _ _] at pay
  have lo:=M.lower
  rw [masks] at lo
  change 4+(headSites y τ).card+(headSites y W).card≤(physicalBlocks c).card at lo
  change (headSites y τ).card=8
  omega

omit [IsStrictOrderedRing K] in
private theorem TrueLocalMode.macro_kernel {a d:K}(L:TrueLocalMode A τ ξ ℓ U a d)
    (T:LocalHeadContrast A b τ h W U Q):
    ℓ∈(blockTotal (localMacroTag A b τ h U)).ker:=by
  classical
  let c:=localMacroTag A b τ h U
  let y:=mirror A
  have good(i:Fin 26)(li:ℓ i≠0):y i=a∧τ i≠0:=by
    have yi:y i=a:=by by_contra e;exact li (L.support i e)
    refine ⟨yi,?_⟩
    intro t
    exact li (by rw [L.values i yi,t,zero_mul])
  have shape(i:Fin 26)(li:ℓ i≠0):c i=(a,Q.eval a,0,0):=by
    obtain ⟨yi,ti⟩:=good i li
    obtain ⟨hh,off⟩:=T.headValue i ti
    change h i=Q.eval (y i) at hh
    change (y i,h i,0,forwardValueTag (reverseHidden b τ U) i)=(a,Q.eval a,0,0)
    rw [hh,yi,forwardValueTag_zero.mpr off]
  have mass:(∑i,ℓ i)=0:=by
    have h:=mem_annih.mp L.paid (1:Vec K 26) (stageWeight_mem_space A .leaf (by decide))
    simpa only [row_apply,Pi.one_apply,mul_one] using h
  change blockTotal c ℓ=0
  funext p
  rw [blockTotal_apply,Pi.zero_apply,Finset.sum_filter]
  by_cases cut:p.val=(a,Q.eval a,0,0)
  · apply Eq.trans _ mass
    apply Finset.sum_congr rfl
    intro i _
    by_cases li:ℓ i=0
    · simp only [li,ite_self]
    · rw [ite_eq_left ((shape i li).trans cut.symm)]
  · apply Finset.sum_eq_zero
    intro i _
    by_cases li:ℓ i=0
    · simp only [li,ite_self]
    · rw [ite_eq_right (fun e=>cut (e.symm.trans (shape i li)))]

private theorem TrueLocalMode.forces_split_of_mass {a d:K}
    (L:TrueLocalMode A τ ξ ℓ U a d)(a0:clockMass (mirror A) τ a≠0):
    ∃i j:Fin 26,τ i≠0∧τ j≠0∧mirror A i=mirror A j∧ξ i≠ξ j:=by
  classical
  let : DecidableEq K:=Classical.decEq K
  obtain ⟨i,hi⟩:∃i,ℓ i≠0:=by by_contra! z;exact L.nonzero (funext z)
  have hiA:mirror A i=a:=by by_contra e;exact hi (L.support i e)
  have hit:τ i≠0:=fun z=>hi (by rw [L.values i hiA,z,zero_mul])
  by_cases spl:∃j:Fin 26,τ j≠0∧mirror A j=a∧ξ i≠ξ j
  · obtain ⟨j,jt,ja,je⟩:=spl
    exact ⟨i,j,hit,jt,hiA.trans ja.symm,je⟩
  have mass:(∑j,ℓ j)=0:=by
    have h:=mem_annih.mp L.paid (1:Vec K 26) (stageWeight_mem_space A .leaf (by decide))
    simpa only [row_apply,Pi.one_apply,mul_one] using h
  have ee:(∑j,ℓ j)=(ξ i-d)*clockMass (mirror A) τ a:=by
    rw [clockMass_apply,Finset.mul_sum,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    by_cases ja:mirror A j=a
    · rw [ite_eq_left ja,L.values j ja]
      by_cases jt:τ j=0
      · rw [jt,zero_mul,mul_zero]
      · have js:ξ i=ξ j:=by by_contra e;exact spl ⟨j,jt,ja,e⟩
        rw [js,mul_comm]
    · rw [ite_eq_right ja,L.support j ja]
  rw [mass,eq_comm] at ee
  have zz:=sub_eq_zero.mp ((mul_eq_zero.mp ee).resolve_right a0)
  exact False.elim (hi (by rw [L.values i hiA,zz,sub_self,mul_zero]))

set_option maxHeartbeats 5300000 in
theorem LocalLinearBand.sixteen_refined_blocks (B:LocalLinearBand A b 2 U τ)
    (ha:StrictLower A)(ho:HasTreeOrderAtLeast A b 17)(S:OddBalanced (s:=25) A b 8)
    (six:7≤finrank K (zeroSpace A 6))(masks:finrank K (reverseHidden b τ U)=4)
    (T:LocalHeadContrast A b τ h W U Q)
    (modes:weightedEval (mirror A) τ (X^7)∈annih (treeSpace A 7) ∨
      (∃a:K,TrueRationalAdvance A τ a) ∨
      (∃a d:K,∃ℓ:Vec K 26,TrueLocalMode A τ ξ ℓ U a d)):
    16≤(refinedHeadBlocks A b τ h ξ U).card:=by
  classical
  let y:=mirror A
  let n:=(headSites y τ).card
  have lb:n≤(refinedHeadBlocks A b τ h ξ U).card:=refined_head_blocks_ge _ _ _ _ _ _
  by_cases many:16≤n
  · exact many.trans lb
  have short:n≤15:=by omega
  have finish (h:∀z∈headSites y τ,clockMass y τ z=0):n=8:=
    B.eight_of_all_clock_masses_zero ha ho S six masks T h
  rcases modes with poly | ⟨a,D⟩ | ⟨a,d,ℓ,L⟩
  · have z:∀x∈headSites y τ,clockMass y τ x=0:=fun x hx=>
      local_mass_zero_of_short_support y τ (l:=14) short (B.polynomial_moments_fourteen poly) hx
    have eight:=finish z
    exact False.elim (B.no_paid_large_orbit ha ho S six eight.ge B.orthogonal
      (B.polynomial_orbit_at_eight poly eight))
  · let ρ:=rationalHead y τ a
    have e:orbitSites y ρ=orbitSites y τ:=D.head_sites
    have z:∀x∈headSites y ρ,clockMass y ρ x=0:=by
      intro x hx
      exact local_mass_zero_of_short_support y ρ (l:=14) (by
        show (orbitSites y ρ).card≤15;rw [e];exact short) (D.moments_fourteen B) hx
    have eight:=finish (D.transfer_zero_mass z)
    have count:8≤(orbitSites y ρ).card:=by rw [e];exact eight.ge
    exact False.elim (B.no_paid_large_orbit ha ho S six count (D.head_orthogonal B) (D.orbit_at_eight B eight))
  have global_no (z:∀x∈headSites y τ,clockMass y τ x=0):False:=by
    have n8:=finish z
    let V:=nodalOrbit y τ
    have Vn:finrank K V=8:=(nodalOrbit_rank _ _).trans n8
    by_cases inV:ℓ∈V
    · let P:=orbitBand y τ 7
      have ext:ℓ∉P:=local_orbitBand_omit y τ ℓ n8.ge L.support L.nonzero
      have exactV:P⊔K∙ℓ=V:=by
        apply Submodule.eq_of_le_of_finrank_le
        · exact sup_le (orbitBand_le _ _ _) ((Submodule.span_singleton_le_iff_mem ..).mpr inV)
        · rw [Submodule.finrank_sup_span_singleton ext,Vn]
          have dd:finrank K P=7:=orbitBand_rank _ _ _ (by change 7≤n;omega)
          rw [dd]
      have v7:V≤annih (treeSpace A 7):=by
        rw [←exactV]
        exact sup_le B.low_orbitBand_paid ((Submodule.span_singleton_le_iff_mem ..).mpr L.paid)
      exact B.no_paid_large_orbit ha ho S six n8.ge B.orthogonal v7
    let c:=localMacroTag A b τ h U
    let N:=V⊔K∙ℓ
    have N0:N≤(blockTotal c).ker:=sup_le (T.orbit_macro_kernel_of_zero_masses z)
      ((Submodule.span_singleton_le_iff_mem ..).mpr (L.macro_kernel T))
    have no:N≤annih U:=by
      apply sup_le _ ((Submodule.span_singleton_le_iff_mem ..).mpr L.orthogonal)
      change nodalOrbit y τ≤_
      rw [nodalOrbit_eq_weightedEval]
      rintro _ ⟨P,rfl⟩
      exact weightedEval_orthogonal B.clock B.orthogonal P
    have M:=B.local_macro_audit ho T
    have price:=rank_with_physical_blocks c U N M.baseZero N0 no
    change finrank K U+finrank K ↥(V⊔K∙ℓ)+(physicalBlocks c).card≤26 at price
    rw [B.dimension,Submodule.finrank_sup_span_singleton inV,Vn] at price
    have lower:=M.lower
    rw [masks] at lower
    change 4+n+(headSites y W).card≤(physicalBlocks c).card at lower
    have wc:4≤(headSites y W).card:=four_sites_of_unit_contrast _ _ _ T.degree T.nonzero T.moments
    omega
  by_cases n14:n≤14
  · exact False.elim (global_no (fun x hx=>local_mass_zero_of_short_support y τ (l:=13) n14
      B.moments_thirteen hx))
  have ex:∃i:Fin 26,ℓ i≠0:=by by_contra! z;exact L.nonzero (funext z)
  obtain ⟨i,li⟩:=ex
  have ia:y i=a:=by by_contra z;exact li (L.support i z)
  have it:τ i≠0:=fun z=>li (by rw [L.values i ia,z,zero_mul])
  have aS:a∈headSites y τ:=ia ▸ headSites_mem i it
  have an:clockMass y τ a≠0:=fun a0=>global_no
    (clockMass_all_zero_of_one y τ (q:=13) short B.moments_thirteen aS a0)
  obtain ⟨i,j,ti,tj,eq,sp⟩:=L.forces_split_of_mass an
  have add:=refined_head_blocks_split (b:=b) (h:=h) (U:=U) i j ti tj eq sp
  change n<(refinedHeadBlocks A b τ h ξ U).card at add
  omega
end
end RKCert.Paired.ReverseHull
