module

public import RKCert.ERKOrderNineLateAggregation

@[expose] public section

/-! # The actual one- and two-dimensional late-column row spaces -/
namespace RKCert.Paired
open Module Polynomial
open scoped Classical

variable {K : Type*} [Field K]

theorem lowState_eq_iff {A : Fin 12→Fin 12→K} {i j : Fin 12} :
    lowStateAt A i=lowStateAt A j ↔
      (qdef A i=0 ↔ qdef A j=0) ∧ nodes A i=nodes A j := by
  by_cases hi : qdef A i=0 <;> by_cases hj : qdef A j=0 <;> simp [lowStateAt,hi,hj]

theorem gather_eq_tagged {A : Fin 12→Fin 12→K} (rep : Fin 12→Fin 10)
    (hr : ∀ i j, rep i=rep j ↔ lowStateAt A i=lowStateAt A j)
    (hRep : ∀ i, rep (lowPrefix10 i)=i) (w : Vec K 12) (i : Fin 10) :
    gatherRow rep w i=if qdef A (lowPrefix10 i)=0 then
      onWeight A w (nodes A (lowPrefix10 i)) else offWeight A w (nodes A (lowPrefix10 i)) := by
  have h (j : Fin 12) : rep j=i ↔ lowStateAt A j=lowStateAt A (lowPrefix10 i) := by
    rw [←hr,hRep]
  by_cases hi : qdef A (lowPrefix10 i)=0
  · rw [gatherRow_apply,ite_eq_left hi,onWeight]
    apply Finset.sum_congr rfl
    intro j _
    simp [h j,lowState_eq_iff,hi]
  · rw [gatherRow_apply,ite_eq_right hi,offWeight]
    apply Finset.sum_congr rfl
    intro j _
    simp [h j,lowState_eq_iff,hi]

theorem gather_annih_restricted {A : Fin 12→Fin 12→K} (rep : Fin 12→Fin 10)
    (h : ∀ i, lowStateAt A i=lowStateAt A (lowPrefix10 (rep i)))
    (U : Submodule K (Vec K 12)) (hU : U≤onOffSpace A)
    {w : Vec K 12} (hw : w∈annih U) :
    gatherRow rep w∈annih (U.map (restrictCol lowPrefix10)) := by
  apply mem_annih.mpr
  rintro _ ⟨v,hv,rfl⟩
  rw [gatherRow_pair]
  have he : restrictCol lowPrefix10 v∘rep=v := by
    ext i
    change v (lowPrefix10 (rep i))=v i
    exact (onOffSpace_eq_at_states (h i) (hU hv)).symm
  rw [he]
  exact mem_annih.mp hw _ hv

theorem finrank_restrict_state {A : Fin 12→Fin 12→K} (rep : Fin 12→Fin 10)
    (h : ∀ i, lowStateAt A i=lowStateAt A (lowPrefix10 (rep i)))
    (U : Submodule K (Vec K 12)) (hU : U≤onOffSpace A) :
    finrank K (U.map (restrictCol lowPrefix10))=finrank K U := by
  let f := (restrictCol lowPrefix10).comp U.subtype
  have hI : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    ext i
    have hp := congrFun he (rep i)
    exact (onOffSpace_eq_at_states (h i) (hU x.property)).trans
      (hp.trans (onOffSpace_eq_at_states (h i) (hU y.property)).symm)
  have hF := LinearMap.finrank_range_of_inj hI
  rw [show f=(restrictCol lowPrefix10).comp U.subtype from rfl,
    LinearMap.range_comp,Submodule.range_subtype] at hF
  exact hF

variable [CharZero K]

theorem clock_E4_to_five_profile {A : Fin 12→Fin 12→K}
    (hF : zeroSpace A 4=chainSpan A (qdef A) 2) {v : Vec K 12}
    (hv : v∈treeSpace A 4) : diag (nodes A) v∈gradeFiveStateSpace A := by
  obtain ⟨P,Q,hP,hQ,he⟩ := treeSpace_four_profile hv hF
  have hdP : (X*P).natDegree≤5 := natDegree_mul_le_of_le (by simp) hP
  have hdQ : (X*Q).natDegree≤3 := natDegree_mul_le_of_le (by simp) hQ
  refine ⟨(fun i => (X*P).coeff i.val,fun i => (X*Q).coeff i.val),?_⟩
  change polyEval A 5 (fun i => (X*P).coeff i.val)+
    diag (qdef A) (polyEval A 3 (fun i => (X*Q).coeff i.val))=_
  rw [←evalNodes_eq_polyEval A _ hdP,←evalNodes_eq_polyEval A _ hdQ,←he]
  ext i
  simp [mul_add]
  ring

theorem prefix_late_one_ne_zero {B : Fin 10→Fin 10→K} (ha : StrictLower B)
    (c b : Vec K 10) (hW : row (diag (1-c) b) 1≠0) :
    lateResidual B c b 1≠0 := by
  intro hz
  let y := (1:Vec K 10)-c
  have hSeed : (2:K) • transMat B (diag y b)-diag y (diag y b) =
      -(2:K) • lateResidual B c b 1 := by
    have eq : (fun i => b i*(1-c i^1)) = diag y b := by ext i; simp [y,mul_comm]
    unfold lateResidual
    rw [eq]
    ext i
    simp only [y,Pi.sub_apply,Pi.add_apply,Pi.neg_apply,Pi.smul_apply,smul_eq_mul,
      Pi.one_apply,diag_apply,Nat.reduceAdd,Nat.cast_ofNat]
    ring
  let U : Submodule K (Vec K 10) := ⊥
  have hT : diag y b∈U := by
    apply mem_of_invariant_seed Fin.revPerm (transMat B) (causal_transpose ha) y b U
    · intro x hx; rw [(Submodule.mem_bot K).mp hx,map_zero]; exact U.zero_mem
    · intro x hx; rw [(Submodule.mem_bot K).mp hx,map_zero]; exact U.zero_mem
    · rw [hSeed,hz,smul_zero]; exact U.zero_mem
  have hZ := (Submodule.mem_bot K).mp hT
  exact hW (by change row (diag y b) 1=0; rw [hZ]; simp [row_apply])

/-- Actual field data for the last scalar calculation. The only row
operators here come from A's first ten physical interactions. -/
structure FixedRadauLateData (A : Fin 12→Fin 12→K) (b : Vec K 12) (P : K[X]) where
  rep : Fin 12→Fin 10
  psi : Vec K 10
  nu : K
  alpha : K
  beta : K
  gamma : K
  psi_nonzero : ∀ i, psi i≠0
  nu_nonzero : nu≠0
  eq1 : lateResidual (prefixMat10 A) (nodes A∘lowPrefix10) (gatherRow rep b) 1=nu • psi
  eq2 : lateResidual (prefixMat10 A) (nodes A∘lowPrefix10) (gatherRow rep b) 2=alpha • psi
  eq3 : lateResidual (prefixMat10 A) (nodes A∘lowPrefix10) (gatherRow rep b) 3=
    fun i => (beta+gamma*nodes A (lowPrefix10 i))*psi i
  off_zero : ∀ i, qdef A (lowPrefix10 i)≠0 → gatherRow rep b i=0
  on_b : ∀ i, qdef A (lowPrefix10 i)=0 →
    gatherRow rep b i=onWeight A b (nodes A (lowPrefix10 i))
  normPsi : ∃ t : K, ∀ i, qdef A (lowPrefix10 i)=0 →
    psi i*P.eval (nodes A (lowPrefix10 i))*nodalSlope (onNodes A) (nodes A (lowPrefix10 i))=t

set_option maxHeartbeats 1000000 in
theorem order9_fixed_radau_late_data
    {A : Fin 12→Fin 12→K} {b : Vec K 12} (ha : StrictLower A)
    (ho : HasTreeOrderAtLeast A b 9)
    (hN : (supportedNodes A (qdef A)).card=5) (hM : (onNodes A).card=5)
    {P : K[X]} (hPd : P.natDegree≤2) (hF : zeroSpace A 4=chainSpan A (qdef A) 2)
    (hP : ∀ i, qdef A i≠0 → P.eval (nodes A i)=qdef A i) :
    Nonempty (FixedRadauLateData A b P) := by
  obtain ⟨hbij,⟨i,hi,hLabel,a,ha0,he⟩,hWOn,hWOff⟩ :=
    order9_ten_distinct_prefix_full ha ho hN hM
  let e := Equiv.ofBijective (fun i => lowStateAt A (lowPrefix10 i)) hbij
  let rep (i : Fin 12) := e.symm (lowStateAt A i)
  have hRep (i : Fin 10) : rep (lowPrefix10 i)=i := e.symm_apply_apply i
  have hRepr (i : Fin 12) : lowStateAt A i=lowStateAt A (lowPrefix10 (rep i)) :=
    (e.apply_symm_apply _).symm
  have hNode (i : Fin 12) : nodes A i=nodes A (lowPrefix10 (rep i)) :=
    stage_node_eq_of_state (hRepr i)
  have hEqRep (i j : Fin 12) : rep i=rep j ↔ lowStateAt A i=lowStateAt A j :=
    e.symm.injective.eq_iff
  let r := orderAdjoint A b 1
  let w := transMat A r
  let psi := gatherRow rep w
  let c := nodes A∘lowPrefix10
  let B := prefixMat10 A
  let b0 := gatherRow rep b
  have hRow : w=a • (A i-A (10:Fin 12)) := by
    change transMat A (orderAdjoint A b 1)=_
    rw [he,map_smul,map_sub,transMat_single_incoming_row,transMat_single_incoming_row]
  have hW (j : Fin 12) (hj : (10:Fin 12)≤j) : w j=0 := by
    rw [hRow,Pi.smul_apply,Pi.sub_apply,ha i j (hi.le.trans hj),ha 10 j hj,sub_self,smul_zero]
  have hiR : lowPrefix10 (rep 10)=i := by
    let j : Fin 10 := ⟨i.val,hi⟩
    have hj : lowPrefix10 j=i := Fin.ext rfl
    have h := (hEqRep i (10:Fin 12)).mpr hLabel
    rw [←hj,hRep] at h
    rw [←h,hj]
  have hPsi : ∀ j, psi j≠0 := by
    intro j
    change gatherRow rep w j≠0
    rw [gather_eq_tagged rep hEqRep hRep]
    by_cases hj : qdef A (lowPrefix10 j)=0
    · rw [ite_eq_left hj]; exact hWOn _ (mem_onNodes.mpr ⟨_,hj,rfl⟩)
    · rw [ite_eq_right hj]; exact hWOff _ (mem_supportedNodes.mpr ⟨_,hj,rfl⟩)
  have hr := orderAdjoint_annih ho (j:=6) (k:=1) (by decide)
  have hw : w∈annih (treeSpace A 5) := transMat_mem_annih_pred hr
  obtain ⟨h5rank,_,_⟩ := order9_five_on_off_stage_five_split ha ho hN hM
  have hRankTen := order9_five_on_off_rank_ten ha ho hN hM
  obtain ⟨hD1,hEnd,_,_,_,_⟩ := order9_rank_five_full ha ho hRankTen
  let V := (gradeFiveStateSpace A).map (restrictCol lowPrefix10)
  let U := (treeSpace A 4).map (restrictCol lowPrefix10)
  have hState5 := gradeFive_profiles_state_valued hP
  have hState4 : treeSpace A 4≤onOffSpace A := by
    intro x hx
    obtain ⟨Q,R,_,_,he⟩ := treeSpace_four_profile hx hF
    exact he ▸ pairProfile_mem_onOffSpace hP Q R
  have hpsi5 : psi∈annih V :=
    gather_annih_restricted rep hRepr _ hState5
      (annih_mono_reverse (gradeFiveStateSpace_le A) hw)
  have hpsi4 : psi∈annih U := gather_annih_restricted rep hRepr _ hState4
    (annih_mono_reverse (treeSpace_mono A (by decide)) hw)
  have hPsiC : diag c psi∈annih U := by
    apply mem_annih.mpr
    rintro _ ⟨x,hx,rfl⟩
    rw [row_flip_diag]
    have hd : diag c (restrictCol lowPrefix10 x)=restrictCol lowPrefix10 (diag (nodes A) x) := rfl
    rw [hd]
    exact mem_annih.mp hpsi5 _ (Submodule.mem_map_of_mem (clock_E4_to_five_profile hF hx))
  have hR5 : finrank K V=9 := (finrank_restrict_state rep hRepr _ hState5).trans h5rank
  have hR4 : finrank K U=8 := by
    obtain ⟨_,_,_,_,hr,_,_,_⟩ := order9_twelve_stage_chart ha ho
    exact (finrank_restrict_state rep hRepr _ hState4).trans hr
  have ha5 : finrank K (annih V)=1 := by have := finrank_add_annih_eq V; omega
  have ha4 : finrank K (annih U)=2 := by have := finrank_add_annih_eq U; omega
  have hPsiN : psi≠0 := fun hz => hPsi 0 (congrFun hz 0)
  have hSpan5 : Submodule.span K {psi}=annih V :=
    Submodule.eq_of_le_of_finrank_le ((Submodule.span_singleton_le_iff_mem ..).mpr hpsi5)
      (by rw [ha5,finrank_span_singleton hPsiN])
  have hInd : diag c psi∉Submodule.span K {psi} := by
    intro hh
    obtain ⟨z,hz⟩ := Submodule.mem_span_singleton.mp hh
    have hConst (i : Fin 10) : c i=z := by
      apply mul_right_cancel₀ (hPsi i)
      exact (congrFun hz i).symm
    have hsub : onNodes A ⊆ ({z}:Finset K) := by
      intro x hx
      obtain ⟨j,_,rfl⟩ := mem_onNodes.mp hx
      simp only [Finset.mem_singleton]
      exact (hNode j).trans (hConst (rep j))
    have hcard := Finset.card_le_card hsub
    simp [hM] at hcard
  have hSpan4 : Submodule.span K {psi} ⊔ Submodule.span K {diag c psi}=annih U :=
    Submodule.eq_of_le_of_finrank_le
      (sup_le ((Submodule.span_singleton_le_iff_mem ..).mpr hpsi4)
        ((Submodule.span_singleton_le_iff_mem ..).mpr hPsiC))
      (by rw [ha4,Submodule.finrank_sup_span_singleton hInd,finrank_span_singleton hPsiN])
  have hCorrection : (fun j => A 10 (lowPrefix10 j)-A (lowPrefix10 (rep 10)) (lowPrefix10 j))
      = (-a⁻¹) • psi := by
    ext j
    rw [hiR]
    have h := gather_prefix_only rep hRep w (hW 10 le_rfl) (hW 11 (by decide)) j
    change psi j=w (lowPrefix10 j) at h
    rw [Pi.smul_apply,smul_eq_mul,h,hRow,Pi.smul_apply,smul_eq_mul,Pi.sub_apply]
    field_simp [ha0]
    ring
  let L := lateResidual B c b0
  have hMove (k : ℕ) : gatherRow rep (orderAdjoint A b k) =
      L k - (b 10*(1-nodes A 10^k)) • ((-a⁻¹) • psi) := by
    rw [gather_adjoint_by_row_difference ha hD1 hEnd rep hRep hNode,hCorrection]
  have addBack (k : ℕ) :
      L k = gatherRow rep (orderAdjoint A b k)+(b 10*(1-nodes A 10^k)) • ((-a⁻¹) • psi) := by
    rw [hMove,sub_add_cancel]
  have h5 (k : ℕ) (hk : k≤2) : L k∈annih V := by
    rw [addBack]
    refine (annih V).add_mem ?_ ((annih V).smul_mem _ ((annih V).smul_mem _ hpsi5))
    exact gather_annih_restricted rep hRepr _ hState5 (annih_mono_reverse
      (gradeFiveStateSpace_le A) (orderAdjoint_annih ho (j:=5) (by omega)))
  have h3 : L 3∈annih U := by
    rw [addBack]
    refine (annih U).add_mem ?_ ((annih U).smul_mem _ ((annih U).smul_mem _ hpsi4))
    exact gather_annih_restricted rep hRepr _ hState4 (orderAdjoint_annih ho (j:=4) (by decide))
  rw [←hSpan4] at h3
  obtain ⟨x,hx,y,hy,hxy⟩ := Submodule.mem_sup.mp h3
  obtain ⟨beta,rfl⟩ := Submodule.mem_span_singleton.mp hx
  obtain ⟨gamma,rfl⟩ := Submodule.mem_span_singleton.mp hy
  have hb : L 1∈Submodule.span K {psi} := hSpan5.symm ▸ h5 1 (by decide)
  obtain ⟨nu,hNu⟩ := Submodule.mem_span_singleton.mp hb
  have hc : L 2∈Submodule.span K {psi} := hSpan5.symm ▸ h5 2 (by decide)
  obtain ⟨alpha,hA⟩ := Submodule.mem_span_singleton.mp hc
  have hb0 : row (diag (1-c) b0) 1≠0 := by
    have he : row (diag (1-c) b0) 1=row b0 (1-c) := by
      simp only [row_apply,diag_apply,Pi.one_apply,Pi.sub_apply,mul_one]
      apply Finset.sum_congr rfl; intro j _; ring
    have ht : (1-c)∘rep=diag (mirror A) (1:Vec K 12) := by
      ext i; simp [c,mirror,hNode i]
    rw [he,show b0=gatherRow rep b from rfl,gatherRow_pair,ht,←row_flip_diag]
    exact back_target_nonzero ho (by decide)
  have hNZ := prefix_late_one_ne_zero (prefixMat10_strict ha) c b0 hb0
  have hNu0 : nu≠0 := by intro h; rw [h,zero_smul] at hNu; exact hNZ hNu.symm
  have hoff : ∀ x∈supportedNodes A (qdef A), offWeight A b x=0 :=
    fun x hx => offWeight_eq_zero_from_head ho P hP (by omega) x hx
  obtain ⟨t,hT⟩ := five_on_annihilator_weight_norm hw hM hPd hP
  refine ⟨⟨rep,psi,nu,alpha,beta,gamma,hPsi,hNu0,hNu.symm,hA.symm,?_,?_,?_,⟨t,?_⟩⟩⟩
  · change L 3=_
    rw [←hxy]
    ext j
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,diag_apply,c,Function.comp_apply]
    ring
  · intro j hj
    rw [gather_eq_tagged rep hEqRep hRep,ite_eq_right hj]
    exact hoff _ (mem_supportedNodes.mpr ⟨_,hj,rfl⟩)
  · intro j hj
    rw [gather_eq_tagged rep hEqRep hRep,ite_eq_left hj]
  · intro j hj
    change gatherRow rep w j * _ * _ = _
    rw [gather_eq_tagged rep hEqRep hRep,ite_eq_left hj]
    exact hT _ (mem_onNodes.mpr ⟨_,hj,rfl⟩)

end RKCert.Paired

