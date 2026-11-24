module
public import RKCert.ReviewedNative.OrderNineCohortMoments

@[expose] public section

/-! # Five clean and five off nodes must have an exceptional terminal axis -/
namespace RKResearch.Certified.Graded.MultiOff
open RKResearch Module Polynomial OneOff Reverse RKCert.Endpoint
open scoped Matrix Classical
variable {K : Type*} [Field K] [CharZero K] {s p : ℕ}

omit [CharZero K] in
/-- The nine independent two-profile directions are already native:
polynomials through degree four on the clean component and degree three
times the quadratic defect on the defective component. -/
theorem gradeFive_nine_state_directions {A : Matrix (Fin s) (Fin s) K} {P : K[X]}
    (m : 5≤(cleanKnots A).card) (n : 4≤(offKnots A).card)
    (fit : ∀i,g A i≠0 → P.eval (nodes A i)=g A i) :
    ∃ U : Submodule K (Fin s→K), finrank K U=9 ∧ U≤gradeFiveStateSpace A ∧ U≤onOffSpace A := by
  let V := (pairBase A 3).range
  have d : finrank K V=9 := by
    unfold V
    rw [LinearMap.finrank_range_of_inj (pairBase_injective m n),Module.finrank_prod,Module.finrank_fin_fun,Module.finrank_fin_fun]
  refine ⟨V,d,?_,?_⟩
  · rintro _ ⟨z,rfl⟩
    rw [pairBase_apply]
    let Q := ofFn 5 z.1
    let R := ofFn 4 z.2
    have dq := ofFn_natDegree_lt (by decide : 1≤5) z.1
    have dr := Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide : 1≤4) z.2)
    refine ⟨(fun i=>Q.coeff i.val,fun i=>R.coeff i.val),?_⟩
    change coeffEval A 5 (fun i=>Q.coeff i.val)+diag (g A) (coeffEval A 3 (fun i=>R.coeff i.val))=
      evalNodes A Q+diag (g A) (evalNodes A R)
    rw [←evalNodes_eq_coeffEval A Q (q:=5) (by change (ofFn 5 z.1).natDegree≤5; omega),
      ←evalNodes_eq_coeffEval A R dr]
  · rintro _ ⟨z,rfl⟩
    rw [pairBase_apply]
    exact pairProfile_mem_onOffSpace fit _ _

omit [CharZero K] in
theorem gradeFive_rankNine_state_valued {A : Matrix (Fin s) (Fin s) K} {P : K[X]}
    (hM : 5 ≤ (cleanKnots A).card) (hN : 4 ≤ (offKnots A).card)
    (hP : ∀ i, g A i≠0 → P.eval (nodes A i)=g A i)
    (hRank : finrank K (treeSpace A 5)=9) : treeSpace A 5 ≤ onOffSpace A := by
  obtain ⟨U,hU,hLe,hState⟩ := gradeFive_nine_state_directions hM hN hP
  have he := Submodule.eq_of_le_of_finrank_le (hLe.trans (gradeFiveStateSpace_le A))
    (by rw [hRank,hU])
  exact he ▸ hState

theorem primitive_zero_from_clean_prefix {A : Matrix (Fin s) (Fin s) K} {i : Fin s} {q : ℕ}
    (ha : ∀i j,i≤j → A i j=0) (hClean : ∀ v∈zeroSpace A (q+1), v i=0)
    (P : K[X]) (hP : P.natDegree≤q) (v : (Fin s→K)) (hv : mat A v i=0)
    (hpre : ∀ j, j < i → P.eval (nodes A j)=v j) :
    (primitive P).eval (nodes A i)=0 := by
  have hEq := hClean _ (primitive_defect A P hP)
  have hz := causal_mat ha i (evalNodes A P-v) (fun j hj => sub_eq_zero.mpr (hpre j hj))
  rw [map_sub,Pi.sub_apply,hv,sub_zero] at hz
  change mat A (evalNodes A P) i-(primitive P).eval (nodes A i)=0 at hEq
  exact (sub_eq_zero.mp hEq).symm.trans hz

omit [CharZero K] in
theorem first_two_on_rows {A : Matrix (Fin s) (Fin s) K} (hm : 3 ≤ (cleanKnots A).card) :
    ∃ i j : Fin s, g A i=0 ∧ g A j=0 ∧
      nodes A i≠0 ∧ nodes A j≠0 ∧ nodes A j≠nodes A i ∧
      (∀ k, k < i → g A k=0 → nodes A k=0) ∧
      (∀ k, k < j → g A k=0 → nodes A k=0 ∨ nodes A k=nodes A i) := by
  let U : Set (Fin s) := {k | g A k=0 ∧ nodes A k≠0}
  have hu : U.Nonempty := exists_nonzero_on_of_card (by omega : 2 ≤ (cleanKnots A).card)
  obtain ⟨i,⟨hdi,hni⟩,hI⟩ := wellFounded_lt.has_min U hu
  let a := nodes A i
  let V : Set (Fin s) := {k | g A k=0 ∧ nodes A k≠0 ∧ nodes A k≠a}
  have hv : V.Nonempty := by
    by_contra h
    have hh : cleanKnots A ⊆ ({0,a}:Finset K) := by
      intro x hx
      obtain ⟨k,hk,rfl⟩ := mem_cleanKnots.mp hx
      by_cases hz : nodes A k=0
      · simp [hz]
      by_cases ha : nodes A k=a
      · simp [ha]
      exact (h ⟨k,hk,hz,ha⟩).elim
    have ht := Finset.card_le_card hh
    rw [Finset.card_pair (Ne.symm hni)] at ht
    omega
  obtain ⟨j,⟨hdj,hnj,hja⟩,hJ⟩ := wellFounded_lt.has_min V hv
  refine ⟨i,j,hdi,hdj,hni,hnj,hja,?_,?_⟩
  · intro k hlt hk
    by_contra hn
    exact hI k ⟨hk,hn⟩ hlt
  · intro k hlt hk
    by_contra! hn
    exact hJ k ⟨hk,hn.1,hn.2⟩ hlt

theorem order9_five_off_five_on_rank_nine_impossible
    {A : Matrix (Fin 12) (Fin 12) K} {b : (Fin 12→K)} (ha : ∀i j,i≤j → A i j=0)
    (ho : HasOrder 9 A b)
    (hN : (offKnots A).card=5) (hM : (cleanKnots A).card=5)
    (hr : finrank K (treeSpace A 5)=9) : False := by
  obtain ⟨P,hPd,hPn,_,hF,hP⟩ := order9_two_curve_head ha ho (by decide) (by omega)
  have hoff : ∀ x∈offKnots A, offMass A b x=0 :=
    fun x hx => offMass_zero_of_head ho hP (by omega) x hx
  have hState := gradeFive_rankNine_state_valued (by omega : 5≤(cleanKnots A).card)
    (by omega : 4≤(offKnots A).card) hP hr
  have hClean (i : Fin 12) (hi : g A i=0) (v : (Fin 12→K))
      (hv : v∈zeroSpace A 5) : v i=0 :=
    state_defect_five_zero_on (s:=11) ha ho hM hoff hv
      (hState (zeroSpace_le_treeSpace A 5 hv)) hi
  obtain ⟨i,j,hi,hj,hni,hnj,hji,hFirst,hSecond⟩ :=
    first_two_on_rows (by omega : 3≤(cleanKnots A).card)
  let u := nodes A i
  let z := nodes A j
  have hu : u≠0 := hni
  have hz : z≠0 := hnj
  have hzu : z≠u := hji
  let v := diag (nodes A) (g A)
  let w := diag (nodes A) v
  have hg1 : v∈zeroSpace A 3 := diag_zeroSpace A 2 (mDef_mem A 1)
  have hg2 : w∈zeroSpace A 4 := diag_zeroSpace A 3 hg1
  have hv (k : Fin 12) (hk : g A k=0) : mat A v k=0 := hClean k hk _
    (zeroSpace_mono A (by decide) (mat_zeroSpace_charZero A 3 hg1))
  have hw (k : Fin 12) (hk : g A k=0) : mat A w k=0 :=
    hClean k hk _ (mat_zeroSpace_charZero A 4 hg2)
  have hdx : (X*P).natDegree≤3 := natDegree_mul_le_of_le (by simp) hPd
  have hdegXX : ((X : K[X])^2).natDegree≤2 := by simp
  have hdxx : (X^2*P).natDegree≤4 := natDegree_mul_le_of_le hdegXX hPd
  have J := primitive_zero_from_clean_prefix ha (q:=4) (hClean i hi)
    (X*P) (by omega) v (hv _ hi) (fun k hk => by
      by_cases h : g A k=0
      · simp [v,hFirst k hk h,h]
      · simp [v,hP k h,mul_comm])
  have U := primitive_zero_from_clean_prefix ha (q:=4) (hClean i hi)
    (X^2*P) hdxx w (hw _ hi) (fun k hk => by
      by_cases h : g A k=0
      · simp [w,v,hFirst k hk h,h]
      · simp [w,v,pow_two,hP k h,mul_assoc])
  let T := X^2*P - C u*(X*P)
  have hTd : T.natDegree≤4 := natDegree_sub_le_of_le hdxx
    ((natDegree_C_mul_le u (X*P)).trans (hdx.trans (by decide : (3:ℕ)≤4)))
  have hT := primitive_zero_from_clean_prefix ha (q:=4) (hClean j hj)
    T hTd (w-u • v) (by rw [map_sub,map_smul,Pi.sub_apply,Pi.smul_apply,hw _ hj,hv _ hj,smul_zero,sub_zero])
    (fun k hk => by
      by_cases h : g A k=0
      · rcases hSecond k hk h with h0|hu'
        · simp [T,w,v,h,h0]
        · rw [show nodes A k=u from hu']
          simp [T,w,v,h,hu']
          ring
      · simp [T,w,v,hP k h]
        ring)
  have hEq : primitive T=primitive (X^2*P) - u • primitive (X*P) := by
    dsimp [T]
    rw [map_sub,←Polynomial.smul_eq_C_mul,map_smul]
  rw [hEq,eval_sub,Polynomial.eval_smul,smul_eq_mul,
    ←scalar_primitive (X^2*P),←scalar_primitive (X*P),
    RKCert.Paired.primitive_eval_X_squared_quadratic P hPd,RKCert.Paired.primitive_eval_X_quadratic P hPd] at hT
  rw [←scalar_primitive (X*P),RKCert.Paired.primitive_eval_X_quadratic P hPd] at J
  rw [←scalar_primitive (X^2*P),RKCert.Paired.primitive_eval_X_squared_quadratic P hPd] at U
  have hp0 := (first_nonzero_on_forces_head_shape ha hF hPd hPn hP ⟨i,hi,hni⟩).1
  have hp' : P.coeff 0≠0 := (coeff_zero_eq_eval_zero P).symm ▸ hp0
  have hratio : z=3*u/4 := RKCert.Paired.on_pair_ratio_of_primitive_tests u z _ _ _ hu hz hzu hp' J U hT
  have hRad := order9_nodal_radau (s:=11) ha ho hM hoff
  have hh := radau_on_root hRad (mem_cleanKnots.mpr ⟨i,hi,rfl⟩) hu
  have hzz := radau_on_root hRad (mem_cleanKnots.mpr ⟨j,hj,rfl⟩) hz
  change RKCert.Paired.radauQuartic.eval z=0 at hzz
  rw [hratio] at hzz
  exact RKCert.Paired.radau_ratio_three_fourths u hh hzz

theorem order9_five_on_off_rank_ten
    {A : Matrix (Fin 12) (Fin 12) K} {b : (Fin 12→K)} (ha : ∀i j,i≤j → A i j=0)
    (ho : HasOrder 9 A b)
    (hN : (offKnots A).card=5) (hM : (cleanKnots A).card=5) :
    finrank K (treeSpace A 5)=10 := by
  have hHi := order9_grade_five_upper ha ho
  obtain ⟨P,_,_,_,_,fit⟩ := order9_two_curve_head ha ho (by decide) (by omega)
  obtain ⟨U,hU,inc,_⟩ := gradeFive_nine_state_directions (by omega : 5≤(cleanKnots A).card)
    (by omega : 4≤(offKnots A).card) fit
  have hLo := Submodule.finrank_mono (inc.trans (gradeFiveStateSpace_le A))
  by_contra h
  exact order9_five_off_five_on_rank_nine_impossible ha ho hN hM (by omega)

theorem order9_five_on_off_stage_five_split
    {A : Matrix (Fin 12) (Fin 12) K} {b : (Fin 12→K)} (ha : ∀i j,i≤j → A i j=0)
    (ho : HasOrder 9 A b)
    (hN : (offKnots A).card=5) (hM : (cleanKnots A).card=5) :
    finrank K (gradeFiveStateSpace A)=9 ∧
      Pi.single (Fin.last 11) 1 ∉ onOffSpace A ∧
      treeSpace A 5 = gradeFiveStateSpace A ⊔ Submodule.span K {Pi.single (Fin.last 11) 1} := by
  obtain ⟨P,_,_,_,_,hP⟩ := order9_two_curve_head ha ho (by decide) (by omega)
  have hoff : ∀ x∈offKnots A, offMass A b x=0 :=
    fun x hx => offMass_zero_of_head ho hP (by omega) x hx
  have hr := order9_five_on_off_rank_ten ha ho hN hM
  obtain ⟨hb,h1,hcoord,_⟩ := order9_rank_five_full_terminal ha ho hr
  have hi : Pi.single (Fin.last 11) 1∈treeSpace A 5 := by
    rwa [←coordinate_as_single]
  have hn : Pi.single (Fin.last 11) 1 ∉ onOffSpace A := fun hw =>
    one_not_on_of_five (s:=11) ha ho hM hoff
      (mem_cleanKnots.mpr ⟨Fin.last 11,on_of_state_single hw hb hoff,h1⟩)
  let U := gradeFiveStateSpace A
  have hnot : Pi.single (Fin.last 11) 1 ∉ U := fun hu => hn (gradeFive_profiles_state_valued hP hu)
  have hLT : U < treeSpace A 5 := lt_of_le_of_ne (gradeFiveStateSpace_le A)
    (fun eq => hnot (eq.symm ▸ hi))
  have hUHi := Submodule.finrank_lt_finrank_of_lt hLT
  obtain ⟨V,hV,hVU,_⟩ := gradeFive_nine_state_directions
    (by omega : 5≤(cleanKnots A).card) (by omega : 4≤(offKnots A).card) hP
  have hULo := Submodule.finrank_mono hVU
  change finrank K V≤finrank K U at hULo
  have hU : finrank K U=9 := by omega
  exact ⟨hU,hn,sup_singleton_eq_of_rank (gradeFiveStateSpace_le A) hi hnot (by
    change finrank K (treeSpace A 5)≤finrank K U+1
    omega)⟩
end RKResearch.Certified.Graded.MultiOff
