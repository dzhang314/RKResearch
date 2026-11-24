module
public import RKCert.ReviewedNative.OrderNineCohortCompression
public import RKCert.ReviewedNative.OrderNineCohortRadauWeights

@[expose] public section

/-! # Physical late-row credit from the ten-cohort Radau chart -/
namespace RKResearch.Certified.Graded.MultiOff
open RKResearch Module Polynomial OneOff Reverse RKCert.Endpoint
open scoped Matrix Classical
variable {K : Type*} [Field K] [CharZero K] {s p : ℕ}

omit [CharZero K] in
theorem clock_E4_to_five_profile {A : Matrix (Fin 12) (Fin 12) K}
    {b : Fin 12→K} (ho : HasOrder 9 A b)
    (hF : zeroSpace A 4=band A 2) {v : (Fin 12→K)}
    (hv : v∈treeSpace A 4) : diag (nodes A) v∈gradeFiveStateSpace A := by
  obtain ⟨P,Q,hP,hQ,he⟩ := treeSpace_four_profile ho hv hF
  have hdP : (X*P).natDegree≤5 := natDegree_mul_le_of_le (by simp) hP
  have hdQ : (X*Q).natDegree≤3 := natDegree_mul_le_of_le (by simp) hQ
  refine ⟨(fun i => (X*P).coeff i.val,fun i => (X*Q).coeff i.val),?_⟩
  change coeffEval A 5 (fun i => (X*P).coeff i.val)+
    diag (g A) (coeffEval A 3 (fun i => (X*Q).coeff i.val))=_
  rw [←evalNodes_eq_coeffEval A _ hdP,←evalNodes_eq_coeffEval A _ hdQ,←he]
  ext i
  simp [mul_add]
  ring

theorem prefix_late_one_ne_zero {B : Matrix (Fin 10) (Fin 10) K} (ha : ∀i j,i≤j → B i j=0)
    (c b : (Fin 10→K)) (hW : row (diag (1-c) b) 1≠0) :
    lateResidual B c b 1≠0 := by
  intro hz
  let y := (1:(Fin 10→K))-c
  have hSeed : (2:K) • transMat B (diag y b)-diag y (diag y b) =
      -(2:K) • lateResidual B c b 1 := by
    have eq : (fun i => b i*(1-c i^1)) = diag y b := by ext i; simp [y,mul_comm]
    unfold lateResidual
    rw [eq]
    ext i
    simp only [y,Pi.sub_apply,Pi.add_apply,Pi.neg_apply,Pi.smul_apply,smul_eq_mul,
      Pi.one_apply,diag_apply,Nat.reduceAdd,Nat.cast_ofNat]
    ring
  let U : Submodule K ((Fin 10→K)) := ⊥
  have hT : diag y b∈U := by
    apply mem_of_invariant_seed Fin.revPerm (transMat B) (causal_transpose ha) y b U
    · intro x hx; rw [(Submodule.mem_bot K).mp hx,map_zero]; exact U.zero_mem
    · intro x hx; rw [(Submodule.mem_bot K).mp hx,map_zero]; exact U.zero_mem
    · rw [hSeed,hz,smul_zero]; exact U.zero_mem
  have hZ := (Submodule.mem_bot K).mp hT
  exact hW (by change row (diag y b) 1=0; rw [hZ]; simp)

/-- Actual field data for the last scalar calculation. The only row
operators here come from A's first ten physical interactions. -/
structure FixedRadauLateData (A : Matrix (Fin 12) (Fin 12) K) (b : (Fin 12→K)) (P : K[X]) where
  rep : Fin 12→Fin 10
  psi : (Fin 10→K)
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
  off_zero : ∀ i, g A (lowPrefix10 i)≠0 → gatherRow rep b i=0
  on_b : ∀ i, g A (lowPrefix10 i)=0 →
    gatherRow rep b i=onWeight A b (nodes A (lowPrefix10 i))
  normPsi : ∃ t : K, ∀ i, g A (lowPrefix10 i)=0 →
    psi i*P.eval (nodes A (lowPrefix10 i))*RKCert.Paired.nodalSlope (cleanKnots A) (nodes A (lowPrefix10 i))=t

set_option maxHeartbeats 1000000 in
theorem order9_fixed_radau_late_data
    {A : Matrix (Fin 12) (Fin 12) K} {b : (Fin 12→K)} (ha : ∀i j,i≤j → A i j=0)
    (ho : HasOrder 9 A b)
    (hN : (offKnots A).card=5) (hM : (cleanKnots A).card=5)
    {P : K[X]} (hPd : P.natDegree≤2) (hF : zeroSpace A 4=band A 2)
    (hP : ∀ i, g A i≠0 → P.eval (nodes A i)=g A i) :
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
    by_cases hj : g A (lowPrefix10 j)=0
    · rw [ite_eq_left hj]; exact hWOn _ (mem_cleanKnots.mpr ⟨_,hj,rfl⟩)
    · rw [ite_eq_right hj]; exact hWOff _ (mem_offKnots.mpr ⟨_,hj,rfl⟩)
  have hr := orderAdjoint_annih ho (j:=6) (k:=1) (by decide)
  have hw : w∈annih (treeSpace A 5) := annih_map_transpose (mat_treeSpace A 5) (Submodule.mem_map_of_mem hr)
  obtain ⟨h5rank,_,_⟩ := order9_five_on_off_stage_five_split ha ho hN hM
  have hRankTen := order9_five_on_off_rank_ten ha ho hN hM
  obtain ⟨hD1,hEnd,_,_,_,_⟩ := Reverse.orderNine_rank_five_full ha ho hRankTen
  let V := (gradeFiveStateSpace A).map (RKCert.Paired.restrictCol lowPrefix10)
  let U := (treeSpace A 4).map (RKCert.Paired.restrictCol lowPrefix10)
  have hState5 := gradeFive_profiles_state_valued hP
  have hState4 : treeSpace A 4≤onOffSpace A := by
    intro x hx
    obtain ⟨Q,R,_,_,he⟩ := treeSpace_four_profile ho hx hF
    exact he ▸ pairProfile_mem_onOffSpace hP Q R
  have hpsi5 : psi∈annih V :=
    gather_annih_restricted rep hRepr _ hState5
      (annih_antitone (gradeFiveStateSpace_le A) hw)
  have hpsi4 : psi∈annih U := gather_annih_restricted rep hRepr _ hState4
    (annih_antitone (treeSpace_mono A (by decide)) hw)
  have hPsiC : diag c psi∈annih U := by
    apply mem_annih.mpr
    rintro _ ⟨x,hx,rfl⟩
    rw [row_flip_diag]
    have hd : diag c (RKCert.Paired.restrictCol lowPrefix10 x)=RKCert.Paired.restrictCol lowPrefix10 (diag (nodes A) x) := rfl
    rw [hd]
    exact mem_annih.mp hpsi5 _ (Submodule.mem_map_of_mem (clock_E4_to_five_profile ho hF hx))
  have hR5 : finrank K V=9 := (finrank_restrict_state rep hRepr _ hState5).trans h5rank
  have hR4 : finrank K U=8 := by
    have hr := (order9_forward_chart ha ho (by decide)).2.2.2.2
    exact (finrank_restrict_state rep hRepr _ hState4).trans hr
  have ha5 : finrank K (annih V)=1 := by have e := finrank_annih V; rw [Fintype.card_fin] at e; change finrank K V+finrank K (annih V)=10 at e; omega
  have ha4 : finrank K (annih U)=2 := by have e := finrank_annih U; rw [Fintype.card_fin] at e; change finrank K U+finrank K (annih U)=10 at e; omega
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
    have hsub : cleanKnots A ⊆ ({z}:Finset K) := by
      intro x hx
      obtain ⟨j,_,rfl⟩ := mem_cleanKnots.mp hx
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
    exact gather_annih_restricted rep hRepr _ hState5 (annih_antitone
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
      simp only [row_apply,dotProduct,diag_apply,Pi.one_apply,Pi.sub_apply,mul_one]
      apply Finset.sum_congr rfl; intro j _; ring
    have ht : (1-c)∘rep=diag (reflectedClock A) (1:(Fin 12→K)) := by
      ext i; simp [c,reflectedClock,hNode i]
    rw [he,show b0=gatherRow rep b from rfl,gatherRow_pair,ht,←row_flip_diag]
    rw [ones_clock ho (by decide)]; exact inv_ne_zero (by norm_num)
  have hNZ := prefix_late_one_ne_zero (prefixMat10_strict ha) c b0 hb0
  have hNu0 : nu≠0 := by intro h; rw [h,zero_smul] at hNu; exact hNZ hNu.symm
  have hoff : ∀ x∈offKnots A, offMass A b x=0 :=
    fun x hx => offMass_zero_of_head ho hP (by omega) x hx
  obtain ⟨t,hT⟩ := five_on_annihilator_weight_norm hw hM hPd hP
  refine ⟨⟨rep,psi,nu,alpha,beta,gamma,hPsi,hNu0,hNu.symm,hA.symm,?_,?_,?_,⟨t,?_⟩⟩⟩
  · change L 3=_
    rw [←hxy]
    ext j
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,diag_apply,c,Function.comp_apply]
    ring
  · intro j hj
    rw [gather_eq_tagged rep hEqRep hRep,ite_eq_right hj]
    exact hoff _ (mem_offKnots.mpr ⟨_,hj,rfl⟩)
  · intro j hj
    rw [gather_eq_tagged rep hEqRep hRep,ite_eq_left hj]
  · intro j hj
    change gatherRow rep w j * _ * _ = _
    rw [gather_eq_tagged rep hEqRep hRep,ite_eq_left hj]
    exact hT _ (mem_cleanKnots.mpr ⟨_,hj,rfl⟩)
end RKResearch.Certified.Graded.MultiOff
