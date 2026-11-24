module
public import RKCert.ERKOddLocalRank
public import RKCert.ERKOddWeightRefund
public import RKCert.ERKOddFourPort

@[expose] public section
/-! # The exceptional actual four-mask, rank-two forward axes
The two branches preserve the same fifth-grade feature h and an actual
sixth-grade ξ. The latter is either localized on one clock or has a true
affine low-feature relation. The ninth ordinary space is paid in both. -/
namespace RKCert.Paired.ReverseHull
open RKCert.Paired.Clock RKCert.Paired.FiniteMidpoint RKCert.Paired.ERKOddHidden
open RKCert.OneEscape RKCert.Endpoint Polynomial Module
variable {K:Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A:Fin 26→Fin 26→K}{b τ:Vec K 26}{U:Submodule K (Vec K 26)}
noncomputable section

theorem invariant_extra_line {s:ℕ}{M V:Submodule K (Vec K s)}{y:Vec K s}
    (inc:M≤V)(dim:finrank K V=finrank K M+1)
    (Mi:M.map (diag y)≤M)(Vi:V.map (diag y)≤V):
    ∃a:K,∃ξ:Vec K s,ξ∈V∧ξ∉M∧V=M⊔K∙ξ∧∀i,y i≠a→ξ i=0:=by
  let T:=V⊓annih M
  have e:V=M⊔T:=nested_dot_complement inc
  have int:M⊓T=⊥:=by
    apply le_bot_iff.mp
    rintro v ⟨u,vt⟩
    exact dot_orthogonal_inter_zero u vt.2
  have rk:finrank K T=1:=by
    have h:=Submodule.finrank_sup_add_finrank_inf_eq M T
    rw [←e,int,finrank_bot,add_zero,dim] at h
    omega
  have inv:T.map (diag y)≤T:=by
    rintro _ ⟨v,hv,rfl⟩
    exact ⟨Vi (Submodule.mem_map_of_mem hv.1),
      diag_annih_invariant Mi (Submodule.mem_map_of_mem hv.2)⟩
  obtain ⟨ξ,ξT,nz⟩:∃v∈T,v≠0:=by
    by_contra! no
    have emp:T=⊥:=le_bot_iff.mp (fun v h=>no v h)
    rw [emp,finrank_bot] at rk
    omega
  have sp:K∙ξ=T:=by
    apply Submodule.eq_of_le_of_finrank_le ((Submodule.span_singleton_le_iff_mem ..).mpr ξT)
    rw [rk,finrank_span_singleton nz]
  have eig:diag y ξ∈K∙ξ:=sp.symm ▸ inv (Submodule.mem_map_of_mem ξT)
  obtain ⟨a,h⟩:=Submodule.mem_span_singleton.mp eig
  refine ⟨a,ξ,ξT.1,fun z=>nz (dot_orthogonal_inter_zero z ξT.2),by rw [sp];exact e,?_⟩
  intro i ne
  have hh:=congrFun h i
  change a*ξ i=y i*ξ i at hh
  exact (mul_eq_zero.mp (show (y i-a)*ξ i=0 by linear_combination -hh)).resolve_left (sub_ne_zero.mpr ne)

structure LocalFourAxis (A:Fin 26→Fin 26→K)(b τ h ξ:Vec K 26)(U:Submodule K (Vec K 26)):Prop where
  fifth:h∈zeroSpace A 5
  headOut:h∉reverseHidden b τ U
  sixth:ξ∈zeroSpace A 6
  axisOut:ξ∉reverseHidden b τ U
  bRefund:∃v∈U,∃P:K[X],P.natDegree≤1∧b*ξ=v+weightedEval (mirror A) τ P
  cleared:∀i,¬Clock.Live (reverseHidden b τ U) i→h i=0→ξ i=0→∀v∈zeroSpace A 9,v i=0
  geometry:(∃a:K,∀i,mirror A i≠a→ξ i=0)∨
    (∃T:K[X],T≠0∧T.natDegree≤1∧(∀j≤2,(diag (nodes A)^j) ξ∈zeroSpace A 6)∧
      ∀i,h i=T.eval (mirror A i)*ξ i)

set_option maxHeartbeats 4400000 in
theorem LocalLinearBand.four_mask_axis (B:LocalLinearBand A b 2 U τ)
    (ha:StrictLower A)(ho:HasTreeOrderAtLeast A b 17)(S:OddBalanced (s:=25) A b 8)
    (live:backSeed1 A b≠0)(masks:finrank K (reverseHidden b τ U)=4)
    (G5:reverseHidden b τ U≤zeroSpace A 5)(f6:finrank K (zeroSpace A 6)=7):
    ∃h ξ:Vec K 26,LocalFourAxis A b τ h ξ U:=by
  let G:=reverseHidden b τ U
  let C:=diag (nodes A)
  let F:=zeroSpace A
  change finrank K G=4 at masks
  change finrank K (F 6)=7 at f6
  have mon:Monotone F:=fun _ _ h=>zeroSpace_mono A h
  have gc:G.map C≤G:=B.hidden_invariant
  have gf:G≤F 8:=B.hidden_pure ho
  have d1:finrank K (back A b 0)=1:=finrank_span_singleton live
  have fin9:finrank K (F 9)≤10:=by
    have w:=S.nextCap
    change finrank K (F 9)+finrank K (back A b 0)≤11 at w
    omega
  obtain ⟨T,tf,tc,maxi⟩:=largest_invariant C (F 8)
  have dt:finrank K T≤5:=invariant_core_cap_of_rank ha ho (by decide) (by decide) S.separated
    S.forwardMid (fin9.trans (by decide:10≤11)) T tf tc
  have GT:G≤T:=maxi _ gf gc
  have tl:4≤finrank K T:=by have d:=Submodule.finrank_mono GT;omega
  by_cases T5:finrank K T=5
  · obtain ⟨h,H⟩:=five_hidden_staircase ha ho (by decide) (by decide) S.separated S.forwardMid
      (fin9.trans (by decide:10≤11)) T5 tf tc
    obtain ⟨a,ξ,ξT,ξout,eq,off⟩:=invariant_extra_line GT (by omega) gc tc
    have ξ6:ξ∈F 6:=H.inside ξT
    have o:∀i,mirror A i≠1-a→ξ i=0:=fun i z=>off i (fun e=>z (by change 1-nodes A i=1-a;rw [e]))
    have v:b*ξ∈U:=by
      apply B.localized (paid_b_times_ordinary_defect (m:=8) ho ξ6 (by decide)) (a:=1-a)
      intro i ni
      simp only [Pi.mul_apply,o i ni,mul_zero]
    refine ⟨h,ξ,⟨H.headGrade,fun h=>H.outside (GT h),ξ6,ξout,⟨b*ξ,v,0,by simp⟩,?_,Or.inl ⟨1-a,o⟩⟩⟩
    intro i nonG h0 ξ0 v hv
    rw [H.top fin9] at hv
    obtain ⟨u,ut,_,_,e⟩:=Clock.exists_head_poly hv
    rw [eq] at ut
    obtain ⟨u₀,ug,v₀,vξ,eq⟩:=Submodule.mem_sup.mp ut
    obtain ⟨a,rfl⟩:=Submodule.mem_span_singleton.mp vξ
    have z:u₀ i=0:=by by_contra n;exact nonG ⟨u₀,ug,n⟩
    rw [e i,←eq,Pi.add_apply,Pi.smul_apply,ξ0,smul_zero,z,h0,mul_zero,add_zero,zero_add]
  have T4:finrank K T=4:=by omega
  have eq:T=G:=(Submodule.eq_of_le_of_finrank_le GT (by omega)).symm
  have escape(j:ℕ)(j6:6≤j)(j8:j≤8):¬(F j).map C≤F j:=by
    intro s
    have hh: F 6≤T:=(mon j6).trans (maxi _ (mon j8) s)
    have d:=Submodule.finrank_mono hh
    change finrank K (F 6)=7 at f6
    omega
  have next(j:ℕ)(j6:6≤j)(j8:j≤8):finrank K (F (j+1))≤finrank K (F j)+1:=by
    have f7:finrank K (F 7)=8:=by
      have g:=strict_rank_interval ha S.separated 6 1 (by decide) (by decide)
      change finrank K (F 6)+1≤finrank K (F 7) at g
      have u:=S.forwardCap 7 (by decide) (by decide)
      change finrank K (F 7)≤8 at u
      change finrank K (F 6)=7 at f6
      omega
    have f8:finrank K (F 8)=9:=S.forwardMid
    interval_cases j
    · change finrank K (F 7)≤finrank K (F 6)+1
      omega
    · change finrank K (F 8)≤finrank K (F 7)+1
      omega
    · change finrank K (F 9)≤finrank K (F 8)+1
      omega
  have b6:finrank K ↥(F 6⊔(F 6).map C)≤finrank K (F 6)+1:=by
    have i:F 6⊔(F 6).map C≤F 7:=sup_le (mon (by decide:6≤7))
      (Submodule.map_le_iff_le_comap.mpr (diag_zeroSpace A 6))
    exact (Submodule.finrank_mono i).trans (next 6 (by decide) (by decide))
  obtain ⟨n,V,ξ,_,vi,v6,vm,base,pow,last,rp⟩:=single_head b6 (escape 6 (by decide) (by decide))
  have vG:V≤G:=eq ▸ maxi _ (v6.trans (mon (by decide:6≤8))) vi
  have gv:G≤V:=vm G gc (G5.trans (mon (by decide:5≤6)))
  have ve:V=G:=le_antisymm vG gv
  have n3:n=3:=by rw [ve,masks] at rp;change finrank K (F 6)=7 at f6;omega
  have flag:F 6=chain C G ξ 3:=by simpa only [ve,n3] using base
  have f9:F 9=chain C G ξ 6:=ordinary_staircase (j:=6) (h:=3) (r:=3) gc (by decide) flag
    (fun k hk=>next (6+k) (by omega) (by omega)) (fun k hk=>escape (6+k) (by omega) (by omega))
    3 (by decide)
  have pows:∀j≤2,(C^j) ξ∈F 6:=fun j hj=>pow j (by omega)
  have ξ6:ξ∈F 6:=by simpa only [pow_zero,one_apply_eq_self] using pows 0 (by decide)
  have ξo:ξ∉G:=fun z=>last ((G5.trans (mon (by decide:5≤6))) (pow_mem gc z n))
  have head:(∃h∈F 5,h∉G):=by
    by_contra! x
    have k:F 5≤G:=fun h hp=>x h hp
    have m:=Submodule.finrank_mono k
    have q:=S.forwardLow 5 (by decide) (by decide)
    change finrank K G=4 at masks
    change 5≤finrank K (F 5) at q
    omega
  obtain ⟨w,hw,wo⟩:=head
  have H:w∈F 6:=mon (by decide:5≤6) hw
  rw [flag] at H
  obtain ⟨v,vG,P,dP,eq⟩:=Clock.exists_head_poly H
  have d:P.natDegree≤2:=by
    by_cases z:P=0
    · simp [z]
    rw [degree_eq_natDegree z] at dP
    have h:P.natDegree<3:=by exact_mod_cast dP
    omega
  have scalar:P=Polynomial.C (P.coeff 0)+Polynomial.C (P.coeff 1)*X+Polynomial.C (P.coeff 2)*X^2:=by
    conv_lhs => rw [P.as_sum_range_C_mul_X_pow' (n:=3) (by omega)]
    simp [Finset.sum_range_succ]
  have de:(C^3) ξ∉F 6:=by simpa only [n3] using last
  have z:P.coeff 2=0:=by
    by_contra ne
    let L:=C w-C v-P.coeff 0•(C ξ)-P.coeff 1•((C^2) ξ)
    have L6:L∈F 6:=by
      have cw:C w∈F 6:=diag_zeroSpace A 5 hw
      have cv:C v∈F 6:=(G5.trans (mon (by decide:5≤6))) (gc (Submodule.mem_map_of_mem vG))
      exact (F 6).sub_mem ((F 6).sub_mem ((F 6).sub_mem cw cv)
        ((F 6).smul_mem _ (pows 1 (by decide)))) ((F 6).smul_mem _ (pows 2 (by decide)))
    have e:L=P.coeff 2•((C^3) ξ):=by
      ext i
      dsimp only [L,C]
      simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,diag_apply,pow_diag_apply]
      have pe:P.eval (nodes A i)=P.coeff 0+P.coeff 1*nodes A i+P.coeff 2*(nodes A i)^2:=by
        conv_lhs => rw [scalar]
        simp only [eval_add,eval_mul,eval_C,eval_X,eval_pow]
      rw [eq i,pe]
      ring
    rw [e] at L6
    exact de (by simpa only [smul_smul,inv_mul_cancel₀ ne,one_smul] using (F 6).smul_mem (P.coeff 2)⁻¹ L6)
  have d1:P.natDegree≤1:=by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j h
    by_cases j2:j=2
    · simpa only [j2] using z
    exact coeff_eq_zero_of_natDegree_lt (by omega)
  let h:=w-v
  have h5:h∈F 5:=(F 5).sub_mem hw (G5 vG)
  have ho':h∉G:=by
    intro z
    apply wo
    have e:w=h+v:=by dsimp only [h];abel
    rw [e];exact G.add_mem z vG
  let L:=reflectPolynomial P
  have fit(i:Fin 26):h i=L.eval (mirror A i)*ξ i:=by
    change h i=(reflectPolynomial P).eval (mirror A i)*ξ i
    rw [eval_mirror_twice]
    change w i-v i=_
    rw [eq i];ring
  have Ln:L≠0:=by
    intro z
    apply ho'
    have zero:h=0:=by ext i;rw [fit i,z,eval_zero,zero_mul,Pi.zero_apply]
    rw [zero];exact G.zero_mem
  obtain ⟨u,uU,Q,dQ,rep⟩:=B.weight_clock_refund ho (j:=6) (by decide) (by decide) 2 pows
  have dQ1:Q.natDegree≤1:=by
    rcases dQ with z|d
    · simp [z]
    · omega
  refine ⟨h,ξ,⟨h5,ho',ξ6,ξo,⟨u,uU,Q,dQ1,rep⟩,?_,
    Or.inr ⟨L,Ln,(reflectPolynomial_degree P).trans d1,pows,fit⟩⟩⟩
  intro i ng h0 ξ0 v v9
  change v∈F 9 at v9
  rw [f9] at v9
  obtain ⟨t,tG,R,_,e⟩:=Clock.exists_head_poly v9
  have tz:t i=0:=by by_contra n;exact ng ⟨t,tG,n⟩
  rw [e i,tz,ξ0,mul_zero,zero_add]

end
end RKCert.Paired.ReverseHull

