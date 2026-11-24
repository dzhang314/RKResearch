module

public import RKCert.ReviewedNative.ERK17LocalFourRank
public import RKCert.ReviewedNative.LocalLinearPaidBorder
public import RKCert.ReviewedNative.NativeClockChainPeel

@[expose] public section

/-! # Actual two-feature geometry in the local four-dimensional case

The exceptional sixth-grade axis preserves the small reverse core and
has an independent, affine output trace. A row off the hidden kernel
where both features vanish kills every genuine F9 column. -/
namespace RKResearch.Certified.ERK17
open RKResearch Module Polynomial Graded Graded.Reverse Graded.Reverse.LocalLinear
open RKCert.Endpoint RKCert.OneEscape
open scoped Classical Matrix
noncomputable section

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A : Matrix (Fin 26) (Fin 26) K} {b τ : Fin 26→K}
variable {U : Submodule K (Fin 26→K)}

set_option maxRecDepth 4000
set_option maxHeartbeats 1350000

structure LocalFourAxes (A : Matrix (Fin 26) (Fin 26) K) (b τ h ξ : Fin 26→K)
    (U : Submodule K (Fin 26→K)) : Prop where
  fifth : h∈zeroSpace A 5
  headOut : h∉hiddenKernel b τ U
  sixth : ξ∈zeroSpace A 6
  axisOut : ξ∉hiddenKernel b τ U
  axisPreserves : U.map (diag ξ)≤U
  weightRefund : ∃ u∈U, ∃ P : K[X], P.natDegree≤1 ∧
    b*ξ=u+weightedEval (reflectedClock A) τ P
  cleared : ∀ i : Fin 26, (∀ v∈hiddenKernel b τ U, v i=0) → h i=0 → ξ i=0 →
    ∀ v∈zeroSpace A 9, v i=0
  geometry : (∃ a : K, ∀ i,reflectedClock A i≠a → ξ i=0) ∨
    (∃ P : K[X], P≠0 ∧ P.natDegree≤1 ∧
      (∀ k≤2,(diag (nodes A)^k) ξ∈zeroSpace A 6) ∧
      h=weightedEval (reflectedClock A) ξ P)

theorem width26_tiny_rank_four_axes
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 17 A b) (nz : firstSeed A b≠0)
    (F : LocalLinearBand A b 7 2 U τ) (full : primitiveBack A b 7=annih (treeSpace A 8))
    (four : finrank K (hiddenKernel b τ U)=4) : ∃ h ξ, LocalFourAxes A b τ h ξ U := by
  let J := hiddenKernel b τ U
  let C := diag (nodes A)
  let G := zeroSpace A
  change finrank K J=4 at four
  have ref := width26_tiny_rank_four_refinement ha ho nz F full four
  have j5 : J≤G 5 := ref.2.1
  have f6 : finrank K (G 6)=7 := ref.2.2
  have jc : J.map C≤J := hiddenKernel_forward_clock_of_band F
  have S := (ordered_width26_full_frame ha ho).1
  have sep := PolySeparated.of_coeff S.separated
  have f8 : finrank K (G 8)=9 := S.middleDefects
  have top := width26_nonzero_forward_nine ha ho nz
  have cap : finrank K (G 9)≤11 := by change finrank K (zeroSpace A 9)≤11; rw [top.2]; decide
  have mono : Monotone G := fun _ _ d=>zeroSpace_mono A d
  obtain ⟨T,t8,tc,maximal⟩ := width26_largest_midpoint_core (A:=A)
  have jt : J≤T := maximal _ (j5.trans (mono (by decide : 5≤8))) jc
  have jtr := Submodule.finrank_mono jt
  have tr : finrank K T≤5 := invariant_core_cap_of_rank (q:=8) ha (by decide)
    S.separated S.middleDefects cap T t8 tc
  have axisPay {ξ : Fin 26→K} (hi : ξ∈G 6) : U.map (diag ξ)≤U :=
    local_core_preserved_at_paid_border ho F full (by decide) (by decide) hi
  by_cases T5 : finrank K T=5
  · obtain ⟨h,H⟩ := five_hidden_staircase ha (by decide : 8≤8) S.separated S.middleDefects cap T5 t8 tc
    obtain ⟨a,ξ,ξT,ξout,split,off⟩ := invariant_codim_one_clock_line jt
      (reflected_invariant_of_ordinary tc) (by omega : finrank K T=finrank K J+1)
    have ξ6 : ξ∈G 6 := H.inside ξT
    have bm : b*ξ∈primitiveBack A b 7 := by
      have w := output_shifted_defect_annih ho (j:=6) (g:=8) (k:=0) (by decide) ξ6
      simpa only [pow_zero,Module.End.one_eq_id,LinearMap.id_apply,←full] using w
    have bu : b*ξ∈U := by
      apply F.local_mem_core (by decide) bm (y:=a)
      intro i ne
      simp only [Pi.mul_apply,off i ne,mul_zero]
    have e8 : G 8=chain C T h 4 := H.midpoint
    have e9 : G 9=chain C T h 5 := by
      have eq := top.1
      change G 9=G 8⊔(G 8).map C at eq
      rw [e8,clock_chain_next tc (by decide : 0<4)] at eq
      exact eq
    refine ⟨h,ξ,⟨H.headGrade,fun bad=>H.outside (jt bad),ξ6,ξout,axisPay ξ6,
      ⟨b*ξ,bu,0,by simp,by simp⟩,?_,Or.inl ⟨a,off⟩⟩⟩
    intro i dead h0 ξ0 v hv
    change v∈G 9 at hv
    rw [e9] at hv
    obtain ⟨z,hz,P,_,expr⟩ := HeadFiber.exists_poly hv
    have zi : z i=0 := by
      rw [split] at hz
      obtain ⟨w,hw,v',hv',rfl⟩ := Submodule.mem_sup.mp hz
      obtain ⟨t,rfl⟩ := Submodule.mem_span_singleton.mp hv'
      simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,dead _ hw,ξ0,mul_zero,add_zero]
    rw [expr]
    simp only [Pi.add_apply,zi,weightedEval_apply,h0,mul_zero,zero_add]
  have eq : T=J := (Submodule.eq_of_le_of_finrank_le jt (by omega)).symm
  have budget : finrank K (G (6+2))≤finrank K (G 6)+2 := by
    change finrank K (G 8) ≤ finrank K (G 6)+2
    omega
  obtain ⟨n,V,ξ,H⟩ := flat_clock_head ha (j:=6) (d:=2) S.separated (by decide) (by decide) budget
  have vt : V≤T := maximal _ (H.coreInside.trans (mono (by decide : 6≤8))) H.coreStable
  have vj : V=J := le_antisymm (eq ▸ vt) (H.coreMaximal _ jc (j5.trans (mono (by decide : 5≤6))))
  have n3 : n=3 := by
    have w := H.baseRank
    rw [vj,four] at w
    change finrank K (G 6)=4+n at w
    omega
  have e6 : G 6=chain C J ξ 3 := by
    simpa only [Nat.add_zero,vj,n3] using H.flags 0 (by decide)
  have e8 : G 8=chain C J ξ 5 := by
    simpa only [vj,n3] using H.flags 2 (by decide)
  have e9 : G 9=chain C J ξ 6 := by
    have nxt := top.1
    change G 9=G 8⊔(G 8).map C at nxt
    rw [e8,clock_chain_next jc (by decide : 0<5)] at nxt
    exact nxt
  have paid (k : ℕ) (hk : k≤2) : (C^k) ξ∈G 6 :=
    ((clock_chain_le_iff 3).mp e6.ge).2 k (by omega)
  have ξ6 : ξ∈G 6 := by simpa only [pow_zero,one_apply_eq_self] using paid 0 (by decide)
  have unpaid : (C^3) ξ∉G 6 := by
    intro h
    have h7 := diag_zeroSpace A 6 h
    have h8 := diag_zeroSpace A 7 h7
    have pow4 : C ((C^3) ξ)=(C^4) ξ := by
      simpa only [Module.End.mul_eq_comp,LinearMap.comp_apply] using
        (congrArg (fun f : Module.End K (Fin 26 → K) => f ξ) (pow_succ' C 3)).symm
    have pow5 : C ((C^4) ξ)=(C^5) ξ := by
      simpa only [Module.End.mul_eq_comp,LinearMap.comp_apply] using
        (congrArg (fun f : Module.End K (Fin 26 → K) => f ξ) (pow_succ' C 4)).symm
    change C (C ((C^3) ξ))∈G 8 at h8
    rw [pow4,pow5] at h8
    exact H.unpaid (by simpa only [n3] using h8)
  have ξout : ξ∉J := by
    intro h
    have stay (n : ℕ) : (C^n) ξ ∈ J := by
      induction n with
      | zero => simpa only [pow_zero,one_apply_eq_self] using h
      | succ n ih =>
        rw [pow_succ',Module.End.mul_eq_comp,LinearMap.comp_apply]
        exact jc (Submodule.mem_map_of_mem ih)
    exact unpaid ((j5.trans (mono (by decide : 5≤6))) (stay 3))
  have e5 : 5≤finrank K (G 5) := grade_five_surplus ha (sep.mono (by decide : 5≤8))
  have notJ : ¬G 5≤J := by
    intro yes
    have d := Submodule.finrank_mono yes
    change finrank K J=4 at four
    omega
  obtain ⟨w,hw,wout⟩ := Set.not_subset.mp notJ
  have h6 : w∈chain C J ξ 3 := e6 ▸ (mono (by decide : 5≤6) hw)
  have d6 : C w∈chain C J ξ 3 := e6 ▸ diag_zeroSpace A 5 hw
  have w2 : w∈chain C J ξ 2 :=
    clock_chain_drop_of_next_unpaid jc 2 (fun e=>unpaid (e6.symm ▸ e)) h6 d6
  obtain ⟨u,hu,P,pd,part⟩ := HeadFiber.exists_poly w2
  have deg : P.natDegree≤1 := by
    by_cases z : P=0
    · simp [z]
    have n := (natDegree_lt_iff_degree_lt z).mpr pd
    omega
  let h := w-u
  let L := P.comp (1-X)
  have h5 : h∈G 5 := (G 5).sub_mem hw (j5 hu)
  have hout : h∉J := by
    intro hh
    change w-u ∈ J at hh
    apply wout
    change w ∈ J
    simpa only [sub_add_cancel] using J.add_mem hh hu
  have fit : h=weightedEval (reflectedClock A) ξ L := by
    have values : weightedEval (nodes A) ξ P=weightedEval (reflectedClock A) ξ L := by
      ext i
      simp [L,weightedEval_apply,eval_comp,reflectedClock]
    dsimp only [h]
    rw [part,add_sub_cancel_left,values]
  have Ld : L.natDegree≤1 := by
    exact natDegree_comp_le.trans (by rw [Thin.one_sub_X_natDegree,mul_one]; exact deg)
  have Ln : L≠0 := by
    intro zz
    apply hout
    rw [fit,zz,map_zero]
    exact J.zero_mem
  obtain ⟨t,ht,Q,qd,out⟩ := local_linear_weight_only_power_refund ho F full (by decide)
    (by decide) (j:=6) (by decide) (by decide) 2 paid
  have dq : Q.natDegree≤1 := by
    rcases qd with qz|d
    · simp [qz]
    · omega
  refine ⟨h,ξ,⟨h5,hout,ξ6,ξout,axisPay ξ6,⟨t,ht,Q,dq,out⟩,?_,
    Or.inr ⟨L,Ln,Ld,paid,fit⟩⟩⟩
  intro i dead _ ξ0 v hv
  change v∈G 9 at hv
  rw [e9] at hv
  obtain ⟨z,hz,P,_,expr⟩ := HeadFiber.exists_poly hv
  rw [expr]
  simp only [Pi.add_apply,dead _ hz,weightedEval_apply,ξ0,mul_zero,zero_add]

end
end RKResearch.Certified.ERK17
