module
public import RKCert.ERKOddLocalContrast
public import RKCert.ERKPrimitiveReverseGain

@[expose] public section
/-! # True next-grade capacity, without asserting a next thin reverse flag -/
namespace RKCert.Paired.ReverseHull
open RKCert.Paired.Clock RKCert.Paired.FiniteMidpoint RKCert.Endpoint Polynomial Module
variable {K:Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A:Fin 26→Fin 26→K}{b τ:Vec K 26}{r:ℕ}{U:Submodule K (Vec K 26)}
noncomputable section

theorem odd17_invariant_reverse_eight_cap (ha:StrictLower A)
    (ho:HasTreeOrderAtLeast A b 17)(S:OddBalanced (s:=25) A b 8)
    (six:7≤finrank K (zeroSpace A 6))
    (W:Submodule K (Vec K 26))(inc:W≤annih (treeSpace A 7))
    (inv:W.map (diag (mirror A))≤W):finrank K W≤8:=by
  let T:=annih (treeSpace A 6)
  have it:W≤T:=inc.trans (annih_antitone_paired (treeSpace_mono A (by decide:6≤7)))
  have mass(v:Vec K 26)(vW:v∈W):(∑i,v i)=0:=by
    have h:=mem_annih.mp (inc vW) (1:Vec K 26) (stageWeight_mem_space A .leaf (by decide))
    simpa only [row_apply,Pi.one_apply,mul_one] using h
  have step:W.map (transMat A)≤T:=by
    rintro _ ⟨v,hv,rfl⟩
    apply mem_annih.mpr
    intro x hx
    rw [row_flip_mat]
    exact mem_annih.mp (inc hv) _ (mat_treeSpace A 6 hx)
  have prim(P:K[X])(pay:P.natDegree+1≤8):reflectedError A b P∈T:=by
    rw [reflectedError_apply]
    exact primitive_annihilator_paid ho P (by omega)
  have H:=outgoing_actual_paid ha ho (r:=4) (by decide) W T it
    (fun a v hv=>Clock.fiber_mem inv a hv) mass step prim
  have dim:=tree_rank_eq ho (S.separated.mono (by decide:6≤8)) (by decide)
  have E:=finrank_annih_eq (treeSpace A 6)
  change finrank K (treeSpace A 6)+finrank K T=26 at E
  omega

theorem LocalLinearBand.head_reflect_paid (B:LocalLinearBand A b r U τ) (m:ℕ)
    (P:K[X])(pay:m+P.natDegree≤15-r):
    weightedEval (mirror A) τ P∈annih (treeSpace A m):=by
  apply mem_annih.mpr
  intro v hv
  have E:=treeSpace_mul hv (mirror_eval_in_tree (A:=A) P (Nat.le_refl _))
  have h:=mem_annih.mp B.paid _ (treeSpace_mono A pay E)
  rw [row_apply] at h ⊢
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.mul_apply,weightedEval_apply]
  ring

/-- The first saturated orbit always overpays the following true marked
annihilator when the sixth ordinary grade has rank at least seven. -/
theorem LocalLinearBand.extra_site_if_six_rich (B:LocalLinearBand A b r U τ)
    (ha:StrictLower A)(ho:HasTreeOrderAtLeast A b 17)(S:OddBalanced (s:=25) A b 8)
    (six:7≤finrank K (zeroSpace A 6)):
    10-r≤(headSites (mirror A) τ).card:=by
  classical
  let : DecidableEq K:=Classical.decEq K
  let y:=mirror A
  let n:=(orbitSites y τ).card
  have lo:9-r≤n:=B.sites
  have rr:r≤2:=by rcases B.short with e|e <;> omega
  change 10-r≤n
  by_contra! few
  have nm:n=9-r:=by omega
  let V:=nodalOrbit y τ
  have VE:orbitBand y τ n=V:=by
    apply Submodule.eq_of_le_of_finrank_le (orbitBand_le y τ n)
    rw [orbitBand_rank y τ n le_rfl,nodalOrbit_rank]
  have val:V≤annih (treeSpace A 7):=by
    rw [←VE]
    rintro _ ⟨a,rfl⟩
    let P:K[X]:=ofFn n a
    have dg:P.natDegree<n:=ofFn_natDegree_lt (by omega) _
    rw [LinearMap.comp_apply]
    exact B.head_reflect_paid 7 P (by omega)
  have ortho:V≤annih U:=by
    change nodalOrbit y τ≤annih U
    rw [nodalOrbit_eq_weightedEval]
    rintro _ ⟨P,rfl⟩
    exact weightedEval_orthogonal B.clock B.orthogonal P
  have inter:U⊓V=⊥:=by
    apply le_bot_iff.mp
    rintro v ⟨u,vv⟩
    exact dot_orthogonal_inter_zero u (ortho vv)
  have Wn:finrank K ↥(U⊔V)=9:=by
    have e:=Submodule.finrank_sup_add_finrank_inf_eq U V
    rw [inter,finrank_bot,add_zero,B.dimension,show finrank K V=n from nodalOrbit_rank _ _] at e
    omega
  have winv:((U⊔V : Submodule K (Vec K 26)).map (diag y))≤U⊔V:=by
    rw [Submodule.map_sup]
    refine sup_le (B.clock.trans le_sup_left) (le_trans ?_ le_sup_right)
    rintro _ ⟨v,hv,rfl⟩
    exact mulByBlock_mem y (nodalOrbit_mask y τ) (fun a=>a) hv
  have bound:=odd17_invariant_reverse_eight_cap ha ho S six (U⊔V)
    (sup_le ((B.base_annih ho).trans (annih_antitone_paired (treeSpace_mono A (by omega:7≤16-r)))) val) winv
  omega
end
end RKCert.Paired.ReverseHull

