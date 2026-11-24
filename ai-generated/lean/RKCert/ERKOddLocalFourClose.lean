module
public import RKCert.ERKOddRefinedLabels
public import RKCert.ERKOddUnitMaskClose

@[expose] public section
/-! # The rank-two four-mask slice ends with exactly four physical ports -/
namespace RKCert.Paired.ReverseHull
open RKCert.Paired.Clock RKCert.Paired.FiniteMidpoint RKCert.Endpoint Module
open scoped Classical
variable {K:Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A:Fin 26→Fin 26→K}{b τ:Vec K 26}{U:Submodule K (Vec K 26)}
noncomputable section

set_option maxHeartbeats 3900000 in
theorem LocalLinearBand.four_forward_masks_impossible (B:LocalLinearBand A b 2 U τ)
    (ha:StrictLower A)(ho:HasTreeOrderAtLeast A b 17)(S:OddBalanced (s:=25) A b 8)
    (live:backSeed1 A b≠0)(masks:finrank K (reverseHidden b τ U)=4)
    (G5:reverseHidden b τ U≤zeroSpace A 5)(f6:finrank K (zeroSpace A 6)=7):False:=by
  obtain ⟨h,ξ,D⟩:=B.four_mask_axis ha ho S live masks G5 f6
  obtain ⟨W,Q,T,val⟩:=B.native_head_contrast_per_stage ho D.fifth D.headOut
  obtain ⟨V,T',axis⟩:=B.refine_by_second_axis ho D T val
  have modes:=B.four_mask_modes ha ho D T'
  have headcount:=B.sixteen_refined_blocks ha ho S f6.ge masks T' modes
  have C:=B.refined_macro_audit ho D T' axis
  let L:=localRefinedTag A b τ h ξ U
  let n:=(refinedHeadBlocks A b τ h ξ U).card
  let w:=(headSites (mirror A) V).card
  have wl:4≤w:=four_sites_of_unit_contrast _ _ _ T'.degree T'.nonzero T'.moments
  have h16:16≤n:=headcount
  have tot:=rank_with_physical_blocks L U ⊥ C.baseZero bot_le bot_le
  rw [B.dimension,finrank_bot,add_zero] at tot
  have lower:=C.lower
  rw [masks] at lower
  change 4+n+w≤(physicalBlocks L).card at lower
  have w4:w=4:=by omega
  have upper:(physicalBlocks L).card≤finrank K (reverseHidden b τ U)+n+w:=by rw [masks];omega
  apply B.no_four_clean_contrast ha ho D.fifth T' w4
  intro i dead bad
  obtain ⟨h0,x0,site⟩:=C.cover upper i dead bad
  exact ⟨site,D.cleared i dead h0 x0⟩

end
end RKCert.Paired.ReverseHull
