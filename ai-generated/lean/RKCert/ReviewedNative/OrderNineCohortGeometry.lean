module
public import RKCert.ReviewedNative.OrderNineCohortRankNine

@[expose] public section

/-! # State values retain every physical coordinate and identify its actual reverse contrast -/
namespace RKResearch.Certified.Graded.MultiOff
open RKResearch Module Polynomial OneOff Reverse RKCert.Endpoint
open scoped Matrix Classical
variable {K : Type*} [Field K] {s p : ℕ}

theorem map_clock_sup_single {A : Matrix (Fin s) (Fin s) K} {U : Submodule K ((Fin s→K))}
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

abbrev LowState (A : Matrix (Fin s) (Fin s) K) :=
  Sum (↥(cleanKnots A)) (↥(offKnots A))

noncomputable def lowStateAt (A : Matrix (Fin s) (Fin s) K) (i : Fin s) : LowState A :=
  if h : g A i=0 then Sum.inl ⟨nodes A i,mem_cleanKnots.mpr ⟨i,h,rfl⟩⟩
  else Sum.inr ⟨nodes A i,mem_offKnots.mpr ⟨i,h,rfl⟩⟩

theorem lowState_card (A : Matrix (Fin s) (Fin s) K) :
    Fintype.card (LowState A)=(cleanKnots A).card+(offKnots A).card := by
  rw [Fintype.card_sum,Fintype.card_coe,Fintype.card_coe]

theorem onOffEval_lowState (A : Matrix (Fin s) (Fin s) K) (z)
    (i : Fin s) : onOffEval A z i=Sum.elim z.1 z.2 (lowStateAt A i) := by
  by_cases h : g A i=0
  · rw [onOffEval_on A _ h,lowStateAt,dite_eq_left h]
    rfl
  · rw [onOffEval_off A _ h,lowStateAt,dite_eq_right h]
    rfl

theorem onOffSpace_eq_at_states {A : Matrix (Fin s) (Fin s) K} {i j : Fin s}
    (hij : lowStateAt A i=lowStateAt A j)
    {v : (Fin s→K)} (hv : v∈onOffSpace A) : v i=v j := by
  obtain ⟨z,rfl⟩ := hv
  rw [onOffEval_lowState,onOffEval_lowState,hij]


theorem lowState_eq_iff {A : Matrix (Fin s) (Fin s) K} {i j : Fin s} :
    lowStateAt A i=lowStateAt A j ↔
      (g A i=0 ↔ g A j=0) ∧ nodes A i=nodes A j := by
  by_cases hi : g A i=0 <;> by_cases hj : g A j=0 <;> simp [lowStateAt,hi,hj]

/-- All physical coordinates are retained. A contrast on two equal-tag
clocks is the actual first unreflected adjoint whenever those coordinates
agree on the literal sixth tree space. Its transpose image cannot vanish:
then only would deletion of an equal incoming row preserve order. -/
theorem order9_contrast_of_pair {A : Matrix (Fin 12) (Fin 12) K} {b : Fin 12→K}
    [CharZero K] (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder A b 9)
    (zero : firstSeed A b=0) (r6 : finrank K (treeSpace A 6)=11)
    {i j : Fin 12} (ij : i<j)
    (same : ∀ u∈treeSpace A 6,u i=u j) :
    ∃ a : K,a≠0 ∧ orderAdjoint A b 1=a • (Pi.single i 1-Pi.single j 1) ∧
      transMat A (orderAdjoint A b 1)≠0 := by
  let v : Fin 12→K := Pi.single i 1-Pi.single j 1
  have inV : v∈annih (treeSpace A 6) := by
    apply mem_annih.mpr
    intro w hw
    change row (Pi.single i 1-Pi.single j 1) w=0
    rw [row_sub_col,row_single_left_eq_coord,row_single_left_eq_coord,same w hw,sub_self]
  have nz : v≠0 := by
    intro e
    have pr := congrFun e i
    simp [v,ne_of_lt ij] at pr
  have rr := finrank_annih (treeSpace A 6)
  rw [Fintype.card_fin] at rr
  have eq : Submodule.span K {v}=annih (treeSpace A 6) :=
    Submodule.eq_of_le_of_finrank_le ((Submodule.span_singleton_le_iff_mem ..).mpr inV)
      (by rw [finrank_span_singleton nz]; omega)
  have adj := orderAdjoint_annih ho (j:=6) (k:=1) (by decide)
  rw [←eq] at adj
  obtain ⟨a,e⟩ := Submodule.mem_span_singleton.mp adj
  have an : a≠0 := by
    intro az
    rw [az,zero_smul] at e
    exact nonzero_orderAdjoint_one ha ho (by decide) zero e.symm
  refine ⟨a,an,e.symm,?_⟩
  intro tz
  rw [←e,map_smul] at tz
  have u := (smul_eq_zero.mp tz).resolve_left an
  apply no_identical_rows_at_uniform_floor ha ho ij
  change transMat A (Pi.single i 1-Pi.single j 1)=0 at u
  rw [map_sub,transMat_single_incoming_row,transMat_single_incoming_row] at u
  exact congrFun (sub_eq_zero.mp u)

variable [CharZero K]

theorem order9_five_on_off_stage_six_split
    {A : Matrix (Fin 12) (Fin 12) K} {b : (Fin 12→K)} (ha : ∀i j,i≤j → A i j=0)
    (ho : HasOrder A b 9)
    (hN : (offKnots A).card=5) (hM : (cleanKnots A).card=5) :
    finrank K (treeSpace A 6)=11 ∧
      treeSpace A 6 = onOffSpace A ⊔ Submodule.span K {Pi.single (Fin.last 11) 1} := by
  have h6 := order9_grade_six_upper ha ho
  obtain ⟨P,_,_,_,_,hP⟩ := order9_two_curve_head ha ho (by decide) (by omega)
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
    apply grade_five_not_stable ha ho
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

theorem order9_five_on_off_reverse_contrast
    {A : Matrix (Fin 12) (Fin 12) K} {b : (Fin 12→K)} (ha : ∀i j,i≤j → A i j=0)
    (ho : HasOrder A b 9)
    (hN : (offKnots A).card=5) (hM : (cleanKnots A).card=5) :
    ∃ i j : Fin 12, i < j ∧ j < Fin.last 11 ∧ lowStateAt A i=lowStateAt A j ∧
      ∃ a : K, a≠0 ∧
        orderAdjoint A b 1 = a • (Pi.single i 1-Pi.single j 1) ∧
        transMat A (orderAdjoint A b 1) ≠ 0 := by
  obtain ⟨r6,shape⟩ := order9_five_on_off_stage_six_split ha ho hN hM
  have r5 := order9_five_on_off_rank_ten ha ho hN hM
  have first := (Reverse.orderNine_rank_five_full ha ho r5).1
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
  refine ⟨i,j,hij,hjl,hijState,?_⟩
  apply order9_contrast_of_pair ha ho first r6 hij
  intro w hw
  rw [shape] at hw
  obtain ⟨u,hu,u',hu',rfl⟩ := Submodule.mem_sup.mp hw
  obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hu'
  have eq := onOffSpace_eq_at_states hijState hu
  have ni : i≠Fin.last 11 := ne_of_lt (hij.trans hjl)
  have nj : j≠Fin.last 11 := ne_of_lt hjl
  change i≠(11:Fin 12) at ni
  change j≠(11:Fin 12) at nj
  simpa [ni,nj] using eq
end RKResearch.Certified.Graded.MultiOff
