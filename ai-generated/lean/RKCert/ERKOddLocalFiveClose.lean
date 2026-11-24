module
public import RKCert.ERKOddMacroMass
public import RKCert.ERKOddUnitMaskClose

@[expose] public section
/-! # Five localized forward masks are impossible at the order-17 boundary -/
namespace RKCert.Paired.ReverseHull
open RKCert.Paired.Clock RKCert.Paired.ERKEvenHidden RKCert.Paired.ERKOddHidden
open RKCert.Paired.FiniteMidpoint RKCert.Endpoint Polynomial Module
variable {K:Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A:Fin 26→Fin 26→K}{b τ:Vec K 26}{r:ℕ}{U:Submodule K (Vec K 26)}
noncomputable section

set_option maxHeartbeats 3800000 in
theorem LocalLinearBand.five_forward_masks_impossible (B:LocalLinearBand A b r U τ)
    (ha:StrictLower A)(ho:HasTreeOrderAtLeast A b 17)(S:OddBalanced (s:=25) A b 8)
    (live:backSeed1 A b≠0)(masks:finrank K (reverseHidden b τ U)=5):False:=by
  classical
  let : DecidableEq K:=Classical.decEq K
  let G:=reverseHidden b τ U
  let c:=nodes A
  let y:=mirror A
  let C:=diag c
  have Gi:G.map C≤G:=B.hidden_invariant
  have Gf:G≤zeroSpace A 8:=B.hidden_pure ho
  have br:finrank K (back A b 0)=1:=finrank_span_singleton live
  have cap:finrank K (zeroSpace A 9)≤10:=by
    have h:=S.nextCap
    change finrank K (zeroSpace A 9)+finrank K (back A b 0)≤11 at h
    omega
  obtain ⟨h,hn⟩:=five_hidden_staircase ha ho (by decide) (by decide) S.separated S.forwardMid
    (cap.trans (by decide:10≤11)) masks Gf Gi
  have f6:7≤finrank K (zeroSpace A 6):=by
    have f8:finrank K (zeroSpace A 8)=9:=S.forwardMid
    have g6:zeroSpace A 6=RKCert.OneEscape.chain C G h 2:=hn.flags 6 (by decide) (by decide)
    have g8:zeroSpace A 8=(zeroSpace A 6⊔K∙((C^2) h))⊔K∙((C^3) h):=by
      rw [g6,hn.midpoint]
      rfl
    have sum (V:Submodule K (Vec K 26))(w:Vec K 26):
        finrank K ↥(V⊔K∙w)≤finrank K V+1:=by
      have d:=Submodule.finrank_sup_add_finrank_inf_eq V (K∙w)
      have t:finrank K ↥(K∙w)≤1:=by
        by_cases z:w=0
        · rw [z,Submodule.span_singleton_eq_bot.mpr rfl,finrank_bot];omega
        · rw [finrank_span_singleton z]
      omega
    rw [g8] at f8
    have a:=sum (zeroSpace A 6) ((C^2) h)
    have b:=sum (zeroSpace A 6⊔K∙((C^2) h)) ((C^3) h)
    omega
  obtain ⟨W,Q,T⟩:=B.native_head_contrast ho hn.headGrade hn.outside
  have M:=B.local_macro_audit ho T
  let L:=localMacroTag A b τ h U
  have sizeWT:4≤(headSites y W).card:=four_sites_of_unit_contrast _ _ _ T.degree T.nonzero T.moments
  have rlo:1≤r∧r≤2:=by rcases B.short with e|e <;> omega
  have big:17-r≤(headSites y τ).card:=B.long_macro_sites ha ho S T f6 masks
  have total:=rank_with_physical_blocks L U ⊥ M.baseZero bot_le bot_le
  rw [B.dimension,finrank_bot,add_zero] at total
  have paid:=M.lower
  change finrank K G+(headSites y τ).card+(headSites y W).card≤(physicalBlocks L).card at paid
  change finrank K G=5 at masks
  have w4:(headSites y W).card=4:=by omega
  have cover:=M.cover (by change (physicalBlocks L).card≤finrank K G+(headSites y τ).card+(headSites y W).card;omega)
  apply B.no_four_clean_contrast ha ho hn.headGrade T w4
  intro i dead bad
  rcases cover i with assigned|profile|clean
  · exact False.elim (dead assigned)
  · exact False.elim (bad profile)
  refine ⟨clean.2.2.2,?_⟩
  intro f fm
  rw [hn.top cap] at fm
  obtain ⟨u,ug,R,_,eq⟩:=Clock.exists_head_poly fm
  have uz:u i=0:=by by_contra n;exact dead ⟨u,ug,n⟩
  rw [eq i,uz,clean.1,mul_zero,zero_add]
end
end RKCert.Paired.ReverseHull
