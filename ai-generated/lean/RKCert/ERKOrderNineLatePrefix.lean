module

public import RKCert.ERKOrderNineFiveRankNine
public import RKCert.ERKLowAdjoint
public import RKCert.ERKOrderNineFixedRadauCharZero

@[expose] public section

/-! # Exact fifth-to-sixth state split and physical reverse contrast

This is the start of the late-column bridge for the fixed-Radau, five-on
five-off branch. Neither the two finite equations nor the exclusion of
that entire branch is claimed here.
-/
namespace RKCert.Paired
open Module Polynomial
open scoped Classical

variable {K : Type*} [Field K] {s p : ℕ}

theorem map_clock_sup_single {A : Fin s → Fin s → K} {U : Submodule K (Vec K s)}
    (h : U.map (diag (nodes A))≤U) (i : Fin s) :
    let W := U ⊔ Submodule.span K {Pi.single i 1}
    W.map (diag (nodes A)) ≤ W := by
  dsimp only
  apply Submodule.map_le_iff_le_comap.mpr
  intro v hv
  obtain ⟨x,hx,y,hy,rfl⟩ := Submodule.mem_sup.mp hv
  obtain ⟨k,rfl⟩ := Submodule.mem_span_singleton.mp hy
  have hd : diag (nodes A) (Pi.single i 1) = nodes A i • Pi.single i 1 := by
    ext j
    by_cases he : j=i <;> simp [he]
  change diag (nodes A) (x+k • Pi.single i 1) ∈ U ⊔ Submodule.span K {Pi.single i 1}
  rw [map_add,map_smul,hd,smul_smul]
  exact Submodule.mem_sup.mpr ⟨_,h (Submodule.mem_map_of_mem hx),_,
    (Submodule.span K {Pi.single i 1}).smul_mem _ (Submodule.mem_span_singleton_self _),rfl⟩

abbrev LowState (A : Fin s → Fin s → K) :=
  Sum (↥(onNodes A)) (↥(supportedNodes A (qdef A)))

noncomputable def lowStateAt (A : Fin s → Fin s → K) (i : Fin s) : LowState A :=
  if h : qdef A i=0 then Sum.inl ⟨nodes A i,mem_onNodes.mpr ⟨i,h,rfl⟩⟩
  else Sum.inr ⟨nodes A i,mem_supportedNodes.mpr ⟨i,h,rfl⟩⟩

theorem lowState_card (A : Fin s → Fin s → K) :
    Fintype.card (LowState A)=(onNodes A).card+(supportedNodes A (qdef A)).card := by
  rw [Fintype.card_sum,Fintype.card_coe,Fintype.card_coe]

theorem onOffEval_lowState (A : Fin s → Fin s → K) (z)
    (i : Fin s) : onOffEval A z i=Sum.elim z.1 z.2 (lowStateAt A i) := by
  by_cases h : qdef A i=0
  · rw [onOffEval_on A _ h,lowStateAt,dite_eq_left h]
    rfl
  · rw [onOffEval_off A _ h,lowStateAt,dite_eq_right h]
    rfl

theorem onOffSpace_eq_at_states {A : Fin s → Fin s → K} {i j : Fin s}
    (hij : lowStateAt A i=lowStateAt A j)
    {v : Vec K s} (hv : v∈onOffSpace A) : v i=v j := by
  obtain ⟨z,rfl⟩ := hv
  rw [onOffEval_lowState,onOffEval_lowState,hij]

theorem row_single_left_eq_coord (w : Vec K s) (i : Fin s) : row (Pi.single i 1) w = w i := by
  rw [row_apply,Finset.sum_eq_single i]
  · simp
  · intro k _ hk; simp [hk]
  · simp

theorem transMat_single_incoming_row (A : Fin s → Fin s → K) (i : Fin s) :
    transMat A (Pi.single i 1)=A i := by
  ext j
  rw [mat_apply,Finset.sum_eq_single i]
  · simp
  · intro k _ hk; simp [hk]
  · simp

theorem backSeed2_ne_zero_of_budget {A : Fin s → Fin s → K} {b : Vec K s}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b p) (hp : 2≤p) :
    backSeed2 A b≠0 := by
  intro hz
  let U : Submodule K (Vec K s) := ⊥
  have hf : diag (mirror A) b ∈ U := by
    apply mem_of_invariant_seed Fin.revPerm (transMat A) (causal_transpose ha)
      (mirror A) b U
    · intro x hx; rw [(Submodule.mem_bot K).mp hx,map_zero]; exact U.zero_mem
    · intro x hx; rw [(Submodule.mem_bot K).mp hx,map_zero]; exact U.zero_mem
    · change backSeed2 A b∈U
      rw [hz]; exact U.zero_mem
  have he : diag (mirror A) b=0 := (Submodule.mem_bot K).mp hf
  exact back_target_nonzero ho hp (by rw [he]; simp [row_apply])

section CharZero
variable [CharZero K]

/-- Actual E6 is all state-valued columns plus the single terminal axis.
This follows from the already checked noninvariance of E5 and does not
assume any shape, multiplicity, or chronological placement of the two
repeated features. -/
theorem order9_five_on_off_stage_six_split
    {A : Fin 12 → Fin 12 → K} {b : Vec K 12} (ha : StrictLower A)
    (ho : HasTreeOrderAtLeast A b 9)
    (hN : (supportedNodes A (qdef A)).card=5) (hM : (onNodes A).card=5) :
    finrank K (treeSpace A 6)=11 ∧
      treeSpace A 6 = onOffSpace A ⊔ Submodule.span K {Pi.single (Fin.last 11) 1} := by
  obtain ⟨_,h3,h4,_,_,_,_,h6⟩ := order9_twelve_stage_chart ha ho
  obtain ⟨P,_,_,_,_,hP⟩ := two_curve_head h3 h4 (by omega)
  obtain ⟨h5,hOut,hEQ⟩ := order9_five_on_off_stage_five_split ha ho hN hM
  let V := gradeFiveStateSpace A
  let C := diag (nodes A)
  let W := V ⊔ V.map C
  have hrs := onOffSpace_rank A
  have hVs : V≤onOffSpace A := gradeFive_profiles_state_valued hP
  have hWs : W≤onOffSpace A := sup_le hVs (by
    rintro _ ⟨v,hv,rfl⟩
    exact onOffSpace_diag (hVs hv))
  have hn : ¬ V.map C≤V := by
    intro h
    apply order9_treeSpace_five_not_clock_invariant ha ho
    rw [hEQ]
    exact map_clock_sup_single h (Fin.last 11)
  have hlt : V < W := lt_of_le_of_ne le_sup_left (fun he =>
    hn ((show V.map C≤W from le_sup_right).trans he.ge))
  have hr := Submodule.finrank_lt_finrank_of_lt hlt
  change finrank K V=9 at h5
  have he : W=onOffSpace A := Submodule.eq_of_le_of_finrank_le hWs (by omega)
  have hG := gradeFiveStateSpace_le A
  have hv6 : V≤treeSpace A 6 := hG.trans (treeSpace_mono A (by decide))
  have hw6 : W≤treeSpace A 6 := sup_le hv6 (by
    rintro _ ⟨x,hx,rfl⟩
    exact diag_treeSpace A 5 (hG hx))
  have hS6 : onOffSpace A≤treeSpace A 6 := he ▸ hw6
  have hTerm : Pi.single (Fin.last 11) 1∈treeSpace A 6 := by
    apply treeSpace_mono A (by decide : 5≤6)
    rw [hEQ]
    exact (show Submodule.span K {Pi.single (Fin.last 11) 1} ≤ _ from le_sup_right)
      (Submodule.mem_span_singleton_self _)
  let U := onOffSpace A ⊔ Submodule.span K {Pi.single (Fin.last 11) 1}
  have hU6 : U≤treeSpace A 6 := sup_le hS6 ((Submodule.span_singleton_le_iff_mem ..).mpr hTerm)
  have hU : finrank K U=11 := by
    change finrank K ↥(onOffSpace A ⊔ Submodule.span K {Pi.single (Fin.last 11) 1})=11
    rw [Submodule.finrank_sup_span_singleton hOut,hrs,hM,hN]
  have hEq := Submodule.eq_of_le_of_finrank_le hU6 (by omega)
  exact ⟨hEq ▸ hU,hEq.symm⟩

/-- In the genuine five-on/five-off branch, the degree-one adjoint
residual is a nonzero physical contrast of two nonterminal rows.
The actual incoming rows cannot coincide. -/
theorem order9_five_on_off_reverse_contrast
    {A : Fin 12 → Fin 12 → K} {b : Vec K 12} (ha : StrictLower A)
    (ho : HasTreeOrderAtLeast A b 9)
    (hN : (supportedNodes A (qdef A)).card=5) (hM : (onNodes A).card=5) :
    ∃ i j : Fin 12, i < j ∧ j < Fin.last 11 ∧ lowStateAt A i=lowStateAt A j ∧
      ∃ a : K, a≠0 ∧
        orderAdjoint A b 1 = a • (Pi.single i 1-Pi.single j 1) ∧
        transMat A (orderAdjoint A b 1) ≠ 0 := by
  obtain ⟨hE6,hS6⟩ := order9_five_on_off_stage_six_split ha ho hN hM
  have dRank := order9_five_on_off_rank_ten ha ho hN hM
  obtain ⟨d1,_,_,_,_,_⟩ := order9_rank_five_full ha ho dRank
  have hAdj := orderAdjoint_annih ho (j:=6) (k:=1) (by decide)
  have hAn : finrank K (annih (treeSpace A 6))=1 := by
    have := finrank_add_annih_eq (treeSpace A 6)
    omega
  have hNAdj : orderAdjoint A b 1 ≠ 0 := by
    rw [orderAdjoint_one_eq_backward_two d1 (by norm_num)]
    exact smul_ne_zero (neg_ne_zero.mpr (inv_ne_zero (by norm_num))) (backSeed2_ne_zero_of_budget ha ho (by decide))
  let f := fun i : Fin 11 => lowStateAt A i.castSucc
  have hf : ¬Function.Injective f := by
    intro h
    have he := Fintype.card_le_of_injective f h
    rw [Fintype.card_fin,lowState_card,hM,hN] at he
    omega
  obtain ⟨x,y,he,hxy⟩ := Function.not_injective_iff.mp hf
  obtain ⟨i,j,hij,hjl,hijState⟩ : ∃ i j : Fin 12, i < j ∧
      j < Fin.last 11 ∧ lowStateAt A i=lowStateAt A j := by
    rcases lt_or_gt_of_ne hxy with h|h
    · exact ⟨x.castSucc,y.castSucc,Fin.castSucc_lt_castSucc_iff.mpr h,Fin.castSucc_lt_last _,he⟩
    · exact ⟨y.castSucc,x.castSucc,Fin.castSucc_lt_castSucc_iff.mpr h,Fin.castSucc_lt_last _,he.symm⟩
  let v : Vec K 12 := Pi.single i 1 - Pi.single j 1
  have hV : v∈annih (treeSpace A 6) := by
    apply mem_annih.mpr
    intro w hw
    rw [hS6] at hw
    obtain ⟨u,hu,u',hu',rfl⟩ := Submodule.mem_sup.mp hw
    obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hu'
    have hq := onOffSpace_eq_at_states hijState hu
    have h1 : row v u=0 := by
      rw [show v=Pi.single i 1-Pi.single j 1 from rfl,row_sub_col,row_single_left_eq_coord,row_single_left_eq_coord]
      exact sub_eq_zero.mpr hq
    have h2 : row v (Pi.single (Fin.last 11) 1)=0 := by
      rw [row_single_eq_coord]
      change (Pi.single i (1:K) : Vec K 12) (Fin.last 11) - (Pi.single j (1:K) : Vec K 12) (Fin.last 11)=0
      have hi : (Fin.last 11 : Fin 12) ≠ i := (ne_of_lt (hij.trans hjl)).symm
      have hj : (Fin.last 11 : Fin 12) ≠ j := (ne_of_lt hjl).symm
      change (11:Fin 12)≠i at hi
      change (11:Fin 12)≠j at hj
      simp [hi,hj]
    rw [map_add,map_smul,h1,h2,smul_zero,add_zero]
  have hVN : v≠0 := by
    intro hz
    have e := congrFun hz i
    simp [v,ne_of_lt hij] at e
  have hEq : Submodule.span K {v} = annih (treeSpace A 6) :=
    Submodule.eq_of_le_of_finrank_le ((Submodule.span_singleton_le_iff_mem ..).mpr hV)
      (by rw [hAn,finrank_span_singleton hVN])
  rw [←hEq] at hAdj
  obtain ⟨a,h⟩ := Submodule.mem_span_singleton.mp hAdj
  have ha0 : a≠0 := by intro hz; rw [hz,zero_smul] at h; exact hNAdj h.symm
  refine ⟨i,j,hij,hjl,hijState,a,ha0,h.symm,?_⟩
  intro hz
  rw [←h,map_smul] at hz
  have he := (smul_eq_zero.mp hz).resolve_left ha0
  apply no_identical_rows_at_uniform_floor ha ho (by decide) hij
  intro k
  change transMat A (Pi.single i 1-Pi.single j 1)=0 at he
  rw [map_sub,transMat_single_incoming_row,transMat_single_incoming_row] at he
  exact congrFun (sub_eq_zero.mp he) k

end CharZero
end RKCert.Paired

