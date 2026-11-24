module

public import RKCert.ERKLowStateMoments

@[expose] public section

/-! # Actual p9 rank-nine exclusion for five off and five on nodes -/
namespace RKCert.Paired
open Module Polynomial
open scoped Classical

variable {K : Type*} [Field K] [CharZero K] {s : ℕ}

omit [CharZero K] in
/-- A coarse five-on/four-off evaluation has a literal nine-dimensional
state-valued space inside the unrestricted degree-five profile. -/
theorem gradeFive_nine_state_directions {A : Fin s → Fin s → K} {P : K[X]}
    (hM : 5 ≤ (onNodes A).card) (hN : 4 ≤ (supportedNodes A (qdef A)).card)
    (hP : ∀ i, qdef A i≠0 → P.eval (nodes A i)=qdef A i) :
    ∃ U : Submodule K (Vec K s), finrank K U=9 ∧ U≤gradeFiveStateSpace A ∧ U≤onOffSpace A := by
  let L : ((Fin 5 → K) × (Fin 4 → K)) →ₗ[K] Vec K s :=
    (polyEval A 4).coprod ((diag (qdef A)).comp (polyEval A 3))
  have hl (z : (Fin 5 → K) × (Fin 4 → K)) :
      L z = evalNodes A (ofFn 5 z.1) + diag (qdef A) (evalNodes A (ofFn 4 z.2)) := by
    rw [evalNodes_ofFn A 4,evalNodes_ofFn A 3]
    rfl
  have hLI : Function.Injective L := by
    apply (injective_iff_map_eq_zero _).mpr
    intro z hz
    let Q := ofFn 5 z.1
    let R := ofFn 4 z.2
    have hdQ : Q.natDegree≤4 := Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) _)
    have hdR : R.natDegree≤3 := Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) _)
    rw [hl] at hz
    have hQi : Q=0 := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' Q (onNodes A)
      (fun x hx => by
        obtain ⟨i,hi,rfl⟩ := mem_onNodes.mp hx
        have he := congrFun hz i
        change Q.eval (nodes A i)+qdef A i*R.eval (nodes A i)=0 at he
        simpa [hi] using he) (by omega)
    have hRi : R=0 := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
      R (supportedNodes A (qdef A)) (fun x hx => by
        obtain ⟨i,hi,rfl⟩ := mem_supportedNodes.mp hx
        have he := congrFun hz i
        change Q.eval (nodes A i)+qdef A i*R.eval (nodes A i)=0 at he
        exact (mul_eq_zero.mp (by simpa [hQi] using he)).resolve_left hi) (by omega)
    exact Prod.ext (injective_ofFn 5 (hQi.trans (ofFn_zero _).symm))
      (injective_ofFn 4 (hRi.trans (ofFn_zero _).symm))
  have hR : finrank K (LinearMap.range L)=9 := by
    rw [LinearMap.finrank_range_of_inj hLI,Module.finrank_prod,
      Module.finrank_fin_fun,Module.finrank_fin_fun]
  refine ⟨LinearMap.range L,hR,?_,?_⟩
  · rintro _ ⟨z,rfl⟩
    let Q := ofFn 5 z.1
    let R := ofFn 4 z.2
    have hQ : Q.natDegree≤5 :=
      (Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide : 1≤5) _)).trans (by decide)
    have hR : R.natDegree≤3 := Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) _)
    refine ⟨(fun j => Q.coeff j.val, fun j => R.coeff j.val),?_⟩
    change polyEval A 5 (fun i => Q.coeff i.val) +
      diag (qdef A) (polyEval A 3 (fun i => R.coeff i.val)) = L z
    rw [hl,←evalNodes_eq_polyEval A Q hQ,←evalNodes_eq_polyEval A R hR]
  · rintro _ ⟨z,rfl⟩
    rw [hl]
    exact pairProfile_mem_onOffSpace hP _ _

theorem gradeFive_rankNine_state_valued {A : Fin s → Fin s → K} {P : K[X]}
    (hM : 5 ≤ (onNodes A).card) (hN : 4 ≤ (supportedNodes A (qdef A)).card)
    (hP : ∀ i, qdef A i≠0 → P.eval (nodes A i)=qdef A i)
    (hRank : finrank K (treeSpace A 5)=9) : treeSpace A 5 ≤ onOffSpace A := by
  obtain ⟨U,hU,hLe,hState⟩ := gradeFive_nine_state_directions hM hN hP
  have he := Submodule.eq_of_le_of_finrank_le (hLe.trans (gradeFiveStateSpace_le A))
    (by rw [hRank,hU])
  exact he ▸ hState

theorem primitive_zero_from_clean_prefix {A : Fin s → Fin s → K} {i : Fin s} {q : ℕ}
    (ha : StrictLower A) (hClean : ∀ v∈zeroSpace A (q+1), v i=0)
    (P : K[X]) (hP : P.natDegree≤q) (v : Vec K s) (hv : mat A v i=0)
    (hpre : ∀ j, j < i → P.eval (nodes A j)=v j) :
    (primitive P).eval (nodes A i)=0 := by
  have hEq := hClean _ (primitive_defect A P hP)
  have hz := causal_mat ha i (evalNodes A P-v) (fun j hj => sub_eq_zero.mpr (hpre j hj))
  rw [map_sub,Pi.sub_apply,hv,sub_zero] at hz
  change mat A (evalNodes A P) i-(primitive P).eval (nodes A i)=0 at hEq
  exact (sub_eq_zero.mp hEq).symm.trans hz

omit [CharZero K] in
theorem primitive_eval_X_squared_quadratic (P : K[X]) (hp : P.natDegree≤2) (u : K) :
    (primitive (X^2*P)).eval u =
      P.coeff 0*u^3/3 + P.coeff 1*u^4/4 + P.coeff 2*u^5/5 := by
  conv_lhs => rw [quadratic_coeff_expand P hp]
  simp only [pow_two,mul_assoc,mul_add,X_mul_monomial,map_add,primitive_monomial,
    eval_add,eval_monomial,Nat.reduceAdd,Nat.cast_ofNat,div_mul_eq_mul_div]

omit [CharZero K] in
theorem first_two_on_rows {A : Fin s → Fin s → K} (hm : 3 ≤ (onNodes A).card) :
    ∃ i j : Fin s, qdef A i=0 ∧ qdef A j=0 ∧
      nodes A i≠0 ∧ nodes A j≠0 ∧ nodes A j≠nodes A i ∧
      (∀ k, k < i → qdef A k=0 → nodes A k=0) ∧
      (∀ k, k < j → qdef A k=0 → nodes A k=0 ∨ nodes A k=nodes A i) := by
  let U : Set (Fin s) := {k | qdef A k=0 ∧ nodes A k≠0}
  have hu : U.Nonempty := exists_nonzero_on_of_card (by omega : 2 ≤ (onNodes A).card)
  obtain ⟨i,⟨hdi,hni⟩,hI⟩ := wellFounded_lt.has_min U hu
  let a := nodes A i
  let V : Set (Fin s) := {k | qdef A k=0 ∧ nodes A k≠0 ∧ nodes A k≠a}
  have hv : V.Nonempty := by
    by_contra h
    have hh : onNodes A ⊆ ({0,a}:Finset K) := by
      intro x hx
      obtain ⟨k,hk,rfl⟩ := mem_onNodes.mp hx
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

set_option maxHeartbeats 900000 in
theorem on_pair_ratio_of_primitive_tests (u z d e f : K)
    (hu : u≠0) (hz : z≠0) (hzu : z≠u) (hd : d≠0)
    (h1 : d*u^2/2 + e*u^3/3 + f*u^4/4=0)
    (h2 : d*u^3/3 + e*u^4/4 + f*u^5/5=0)
    (h3 : d*z^3/3 + e*z^4/4 + f*z^5/5 -
      u*(d*z^2/2 + e*z^3/3 + f*z^4/4)=0) :
    z=3*u/4 := by
  have a : d/2 + e*u/3 + f*u^2/4=0 := by
    apply (mul_eq_zero.mp (show u^2*(d/2+e*u/3+f*u^2/4)=0 by linear_combination h1)).resolve_left
    exact pow_ne_zero _ hu
  have b : d/3 + e*u/4 + f*u^2/5=0 := by
    apply (mul_eq_zero.mp (show u^3*(d/3+e*u/4+f*u^2/5)=0 by linear_combination h2)).resolve_left
    exact pow_ne_zero _ hu
  have c : e*u = -4*d := by linear_combination 48*a - 60*b
  have g : 3*f*u^2=10*d := by linear_combination -180*a + 240*b
  have hx : (d*z^2*(z-u)^2)*(4*z-3*u)=0 := by
    linear_combination 6*u^2*h3 - (3*u*z^4/2-2*u^2*z^3)*c -
      (2*z^5/5-u*z^4/2)*g
  have h := (mul_eq_zero.mp hx).resolve_left
    (mul_ne_zero (mul_ne_zero hd (pow_ne_zero _ hz)) (pow_ne_zero _ (sub_ne_zero.mpr hzu)))
  apply (eq_div_iff (by norm_num : (4:K)≠0)).mpr
  linear_combination h

set_option maxHeartbeats 500000 in
/-- The manuscript's feature-valued p9 five-on/five-off branch, with all
conditions derived from the actual tableau. Rank ten remains separate. -/
theorem order9_five_off_five_on_rank_nine_impossible
    {A : Fin 12 → Fin 12 → K} {b : Vec K 12} (ha : StrictLower A)
    (ho : HasTreeOrderAtLeast A b 9)
    (hN : (supportedNodes A (qdef A)).card=5) (hM : (onNodes A).card=5)
    (hr : finrank K (treeSpace A 5)=9) : False := by
  obtain ⟨_,h3,h4,_,_,_,_,_⟩ := order9_twelve_stage_chart ha ho
  obtain ⟨P,hPd,hPn,_,hF,hP⟩ := two_curve_head h3 h4 (by omega)
  have hoff : ∀ x∈supportedNodes A (qdef A), offWeight A b x=0 :=
    fun x hx => offWeight_eq_zero_from_head ho P hP (by omega) x hx
  have hState := gradeFive_rankNine_state_valued (by omega : 5≤(onNodes A).card)
    (by omega : 4≤(supportedNodes A (qdef A)).card) hP hr
  have hClean (i : Fin 12) (hi : qdef A i=0) (v : Vec K 12)
      (hv : v∈zeroSpace A 5) : v i=0 :=
    state_defect_five_zero_on (s:=11) ha ho hM hoff hv
      (hState (zeroSpace_le_treeSpace A 5 hv)) hi
  obtain ⟨i,j,hi,hj,hni,hnj,hji,hFirst,hSecond⟩ :=
    first_two_on_rows (by omega : 3≤(onNodes A).card)
  let u := nodes A i
  let z := nodes A j
  have hu : u≠0 := hni
  have hz : z≠0 := hnj
  have hzu : z≠u := hji
  let g := qdef A
  let v := signal A g 1
  let w := signal A g 2
  have hg1 : v∈zeroSpace A 3 := chainSpan_le_zeroSpace (qdef_mem A) 1
    (signal_mem_chainSpan A _ le_rfl)
  have hg2 : w∈zeroSpace A 4 := chainSpan_le_zeroSpace (qdef_mem A) 2
    (signal_mem_chainSpan A _ le_rfl)
  have hv (k : Fin 12) (hk : qdef A k=0) : mat A v k=0 := hClean k hk _
    (zeroSpace_mono A (by decide) (mat_zeroSpace_charZero A 3 hg1))
  have hw (k : Fin 12) (hk : qdef A k=0) : mat A w k=0 :=
    hClean k hk _ (mat_zeroSpace_charZero A 4 hg2)
  have hdx : (X*P).natDegree≤3 := natDegree_mul_le_of_le (by simp) hPd
  have hdegXX : ((X : K[X])^2).natDegree≤2 := by simp
  have hdxx : (X^2*P).natDegree≤4 := natDegree_mul_le_of_le hdegXX hPd
  have J := primitive_zero_from_clean_prefix ha (q:=4) (hClean i hi)
    (X*P) (by omega) v (hv _ hi) (fun k hk => by
      by_cases h : qdef A k=0
      · simp [v,signal,g,hFirst k hk h,h]
      · simp [v,signal,g,hP k h,mul_comm])
  have U := primitive_zero_from_clean_prefix ha (q:=4) (hClean i hi)
    (X^2*P) hdxx w (hw _ hi) (fun k hk => by
      by_cases h : qdef A k=0
      · simp [w,signal,g,hFirst k hk h,h]
      · simp [w,signal,g,hP k h,mul_comm])
  let T := X^2*P - C u*(X*P)
  have hTd : T.natDegree≤4 := natDegree_sub_le_of_le hdxx
    ((natDegree_C_mul_le u (X*P)).trans (hdx.trans (by decide : (3:ℕ)≤4)))
  have hT := primitive_zero_from_clean_prefix ha (q:=4) (hClean j hj)
    T hTd (w-u • v) (by rw [map_sub,map_smul,Pi.sub_apply,Pi.smul_apply,hw _ hj,hv _ hj,smul_zero,sub_zero])
    (fun k hk => by
      by_cases h : qdef A k=0
      · rcases hSecond k hk h with h0|hu'
        · simp [T,w,v,g,signal,h,h0]
        · rw [show nodes A k=u from hu']
          simp [T,w,v,g,signal,h,hu']
          ring
      · simp [T,w,v,g,signal,hP k h]
        ring)
  have hEq : primitive T=primitive (X^2*P) - u • primitive (X*P) := by
    dsimp [T]
    rw [map_sub,←Polynomial.smul_eq_C_mul,map_smul]
  rw [hEq,eval_sub,Polynomial.eval_smul,smul_eq_mul,
    primitive_eval_X_squared_quadratic P hPd,primitive_eval_X_quadratic P hPd] at hT
  rw [primitive_eval_X_quadratic P hPd] at J
  rw [primitive_eval_X_squared_quadratic P hPd] at U
  have hp0 := (first_nonzero_on_forces_head_shape ha hF hPd hPn hP ⟨i,hi,hni⟩).1
  have hp' : P.coeff 0≠0 := (coeff_zero_eq_eval_zero P).symm ▸ hp0
  have hratio : z=3*u/4 := on_pair_ratio_of_primitive_tests u z _ _ _ hu hz hzu hp' J U hT
  have hRad := order9_nodal_radau (s:=11) ha ho hM hoff
  have hh := radau_on_root hRad (mem_onNodes.mpr ⟨i,hi,rfl⟩) hu
  have hzz := radau_on_root hRad (mem_onNodes.mpr ⟨j,hj,rfl⟩) hz
  change radauQuartic.eval z=0 at hzz
  rw [hratio] at hzz
  exact radau_ratio_three_fourths u hh hzz

theorem order9_five_on_off_rank_ten
    {A : Fin 12 → Fin 12 → K} {b : Vec K 12} (ha : StrictLower A)
    (ho : HasTreeOrderAtLeast A b 9)
    (hN : (supportedNodes A (qdef A)).card=5) (hM : (onNodes A).card=5) :
    finrank K (treeSpace A 5)=10 := by
  obtain ⟨_,_,_,_,_,hLo,hHi,_⟩ := order9_twelve_stage_chart ha ho
  by_contra h
  exact order9_five_off_five_on_rank_nine_impossible ha ho hN hM (by omega)

omit [CharZero K] in
theorem gradeFive_profiles_state_valued {A : Fin s → Fin s → K} {P : K[X]}
    (hP : ∀ i, qdef A i≠0 → P.eval (nodes A i)=qdef A i) :
    gradeFiveStateSpace A≤onOffSpace A := by
  rintro _ ⟨z,rfl⟩
  rw [gradeFiveStateMap_eq_eval]
  exact pairProfile_mem_onOffSpace hP _ _

/-- Exact ten-dimensional split: the actual terminal coordinate is not
state-valued, and accounts for the one extra direction beyond the profile. -/
theorem order9_five_on_off_stage_five_split
    {A : Fin 12 → Fin 12 → K} {b : Vec K 12} (ha : StrictLower A)
    (ho : HasTreeOrderAtLeast A b 9)
    (hN : (supportedNodes A (qdef A)).card=5) (hM : (onNodes A).card=5) :
    finrank K (gradeFiveStateSpace A)=9 ∧
      Pi.single (Fin.last 11) 1 ∉ onOffSpace A ∧
      treeSpace A 5 = gradeFiveStateSpace A ⊔ Submodule.span K {Pi.single (Fin.last 11) 1} := by
  obtain ⟨hb,h3,h4,_,_,_,_,_⟩ := order9_twelve_stage_chart ha ho
  obtain ⟨P,_,_,_,_,hP⟩ := two_curve_head h3 h4 (by omega)
  have hoff : ∀ x∈supportedNodes A (qdef A), offWeight A b x=0 :=
    fun x hx => offWeight_eq_zero_from_head ho P hP (by omega) x hx
  have hr := order9_five_on_off_rank_ten ha ho hN hM
  obtain ⟨_,h1,hi,_,_,_⟩ := order9_rank_five_full ha ho hr
  have hn : Pi.single (Fin.last 11) 1 ∉ onOffSpace A := fun hw =>
    one_not_on_of_five (s:=11) ha ho hM hoff
      (mem_onNodes.mpr ⟨Fin.last 11,on_of_state_single hw hb hoff,h1⟩)
  let U := gradeFiveStateSpace A
  have hnot : Pi.single (Fin.last 11) 1 ∉ U := fun hu => hn (gradeFive_profiles_state_valued hP hu)
  have hLT : U < treeSpace A 5 := lt_of_le_of_ne (gradeFiveStateSpace_le A)
    (fun eq => hnot (eq.symm ▸ hi))
  have hUHi := Submodule.finrank_lt_finrank_of_lt hLT
  obtain ⟨V,hV,hVU,_⟩ := gradeFive_nine_state_directions
    (by omega : 5≤(onNodes A).card) (by omega : 4≤(supportedNodes A (qdef A)).card) hP
  have hULo := Submodule.finrank_mono hVU
  change finrank K V≤finrank K U at hULo
  have hU : finrank K U=9 := by omega
  exact ⟨hU,hn,sup_singleton_eq_of_rank (gradeFiveStateSpace_le A) hi hnot (by
    change finrank K (treeSpace A 5)≤finrank K U+1
    omega)⟩

end RKCert.Paired

