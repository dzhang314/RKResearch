module
public import RKCert.ReviewedNative.OrderNineSixOnK8

@[expose] public section

/-! # Physical order-nine first nonzero clean node has only fifth and sixth placements -/
namespace RKResearch.Certified.Graded.MultiOff
open RKResearch Module Polynomial OneOff Reverse RKCert.Endpoint
open scoped Matrix Classical
variable {K : Type*} [Field K] {s : ℕ}

variable [CharZero K]
theorem degree_three_actual_mat_profile {A : Matrix (Fin s) (Fin s) K}
    (hF : zeroSpace A 4=band A 2)
    (Q R : K[X]) (dQ : Q.natDegree≤3) (dR : R.natDegree≤1) :
    ∃ J : K[X], J.natDegree≤2 ∧
      mat A (evalNodes A Q+diag (g A) (evalNodes A R))=
        evalNodes A (primitive Q)+diag (g A) (evalNodes A J) := by
  have hr : diag (g A) (evalNodes A R)∈zeroSpace A 3 :=
    band_le A 1 (band_iff.mpr ⟨R,dR,rfl⟩)
  have hQ := primitive_defect A Q dQ
  have hv := (zeroSpace A 4).add_mem hQ (mat_zeroSpace_charZero A 3 hr)
  rw [hF,band_iff] at hv
  obtain ⟨J,hJ,eJ⟩ := hv
  refine ⟨J,hJ,?_⟩
  rw [map_add,←eJ]
  abel

theorem quadratic_head_not_dvd_own_weighted_primitive {P : K[X]}
    (dP : P.natDegree=2) (h0 : P.eval 0≠0) : ¬P∣primitive (X*P) := by
  rw [←scalar_primitive]
  exact RKCert.Paired.quadratic_head_not_dvd_own_weighted_primitive dP h0

theorem first_nonzero_on_at_least_fifth {A : Matrix (Fin 12) (Fin 12) K}
    (ha : ∀i j,i≤j → A i j=0) (hF : zeroSpace A 4=band A 2)
    {P : K[X]} (fit : ∀ j,g A j≠0 → P.eval (nodes A j)=g A j)
    {i : Fin 12} (hi : g A i=0) (hn : nodes A i≠0)
    (before : ∀ j : Fin 12, j < i → g A j = 0 → nodes A j = 0) : 4 ≤ i.val := by
  by_contra! small
  let F := (Finset.univ : Finset (Fin 12)).filter (fun j => j < i ∧ g A j ≠ 0)
  let S := F.image (nodes A)
  have s2 : S.card≤2 := by
    have subset : S⊆({nodes A (1:Fin 12),nodes A (2:Fin 12)}:Finset K) := by
      intro x hx
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨pre,off⟩ := (Finset.mem_filter.mp hj).2
      have jl : j.val < i.val := pre
      have nz : j.val≠0 := by
        intro h
        have e : j=(0:Fin 12) := Fin.ext (by simpa using h)
        exact off (e.symm ▸ origin_zeroSpace ha 2 (mDef_mem A 1))
      have e : j=(1:Fin 12) ∨ j=(2:Fin 12) := by
        have h : j.val=1 ∨ j.val=2 := by omega
        exact h.imp Fin.ext Fin.ext
      rcases e with rfl|rfl <;> simp
    exact (Finset.card_le_card subset).trans ((Finset.card_insert_le _ _).trans (by simp))
  let y (x : K) := x/P.eval x
  let R := Lagrange.interpolate S id y
  have dr : R.natDegree≤1 := by
    by_cases h : R=0
    · simp [h]
    · have d := (natDegree_lt_iff_degree_lt h).mpr (Lagrange.degree_interpolate_lt y (Set.injOn_id _))
      omega
  let W := diag (g A) (evalNodes A R)
  have w4 : mat A W∈zeroSpace A 4 := mat_zeroSpace_charZero A 3
    (band_le A 1 (band_iff.mpr ⟨R,dr,rfl⟩))
  rw [hF,band_iff] at w4
  obtain ⟨T,_,he⟩ := w4
  have wt : mat A W i=0 := by simpa [hi] using congrFun he i
  have same (j : Fin 12) (hj : j < i) : nodes A j=W j := by
    by_cases h : g A j=0
    · simp [W,h,before j hj h]
    · have js : nodes A j∈S := Finset.mem_image.mpr
        ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj,h⟩,rfl⟩
      have eqe := Lagrange.eval_interpolate_at_node y (Set.injOn_id _) js
      change R.eval (nodes A j)=y (nodes A j) at eqe
      change nodes A j=g A j*R.eval (nodes A j)
      rw [eqe]
      change nodes A j=g A j*(nodes A j/P.eval (nodes A j))
      rw [fit _ h,mul_div_cancel₀ _ h]
  have z := causal_mat ha i (nodes A-W) (fun j hj => sub_eq_zero.mpr (same j hj))
  rw [map_sub,Pi.sub_apply,wt,sub_zero] at z
  rw [g_apply,z,zero_sub,neg_eq_zero] at hi
  exact div_ne_zero (pow_ne_zero _ hn) (by norm_num) hi

omit [CharZero K] in
theorem first_prefix_state_ne_terminal
    (i : Fin 10) : lowPrefix10 i≠Fin.last 11 := by
  intro h
  have e := congrArg Fin.val h
  change i.val=11 at e
  omega

omit [CharZero K] in
theorem first_prefix_clean_value_ne_one {A : Matrix (Fin 12) (Fin 12) K}
    (last : ∀j,g A j=0 → nodes A j=1 → j=Fin.last 11)
    (i : Fin 10) (on : g A (lowPrefix10 i)=0) : nodes A (lowPrefix10 i)≠1 :=
  fun e => first_prefix_state_ne_terminal i (last _ on e)

section Ordered
variable [LinearOrder K] [IsStrictOrderedRing K]

omit [CharZero K] in
theorem order9_actual_quadratic_first_on_fifth_or_sixth
    {A : Matrix (Fin 12) (Fin 12) K} {b : (Fin 12→K)}
    (ha : ∀i j,i≤j → A i j=0) (ho : HasOrder 9 A b)
    (hM : (cleanKnots A).card=6) (hN : (offKnots A).card=5)
    (hF : zeroSpace A 4=band A 2)
    {P : K[X]} (dP : P.natDegree=2) (pn : P≠0)
    (fit : ∀ j,g A j≠0 → P.eval (nodes A j)=g A j)
    (fg : ActualSixOnFG A P) : fg.first.val=4 ∨ fg.first.val=5 := by
  let _ : DecidableEq K := fun _ _ => Classical.propDecidable _
  let j := lowPrefix10 fg.first
  let h := nodes A j
  have pre (i : Fin 12) (hi : i<j) (g : g A i=0) : nodes A i=0 := by
    have li : i.val<10 := lt_trans hi fg.first.isLt
    let ie : Fin 10 := ⟨i.val,li⟩
    have e : lowPrefix10 ie=i := Fin.ext rfl
    have e' : ie<fg.first := hi
    have t := fg.first_min ie e' (e ▸ g)
    simpa only [e] using t
  have low := first_nonzero_on_at_least_fifth ha hF fit fg.first_clean fg.first_nonzero pre
  change 4≤fg.first.val at low
  by_contra! hs
  have late : 6≤fg.first.val := by omega
  obtain ⟨_,_,_,_,_,_,last⟩ := order9_five_six_stage_chart ha ho hN hM fit
  obtain ⟨bij,_,_,_⟩ := order9_five_six_ten_distinct_prefix ha ho hN hM
  change Function.Bijective (fun i : Fin 10=>lowNonterminalStateAt ha (lowPrefix10 i)) at bij
  have clean1 (i : Fin 10) (hi : g A (lowPrefix10 i)=0) : nodes A (lowPrefix10 i)≠1 :=
    first_prefix_clean_value_ne_one last i hi
  have zeroD : g A (lowPrefix10 0)=0 := origin_zeroSpace ha 2 (mDef_mem A 1)
  have zeroC : nodes A (lowPrefix10 0)=0 := by
    change (∑ j,A (0:Fin 12) j*1)=0
    exact Finset.sum_eq_zero fun j _=>by rw [ha 0 j (Fin.zero_le _),zero_mul]
  let f (i : Fin 5) : Fin 10 := Fin.castLE (by decide : 6≤10) i.succ
  have pr (i : Fin 5) : f i<fg.first := by
    change i.val+1<fg.first.val
    have := i.isLt
    omega
  have off (i : Fin 5) : g A (lowPrefix10 (f i))≠0 := by
    intro g
    have n := fg.first_min (f i) (pr i) g
    have e : lowStateAt A (lowPrefix10 (f i))=lowStateAt A (lowPrefix10 0) :=
      lowState_eq_iff.mpr ⟨by rw [g,zeroD],n.trans zeroC.symm⟩
    have fi := bij.1 ((lowNonterminalState_eq_iff ha (clean1 _) (clean1 _)).mpr e)
    have t := congrArg Fin.val fi
    change i.val+1=0 at t
    omega
  have inj : Function.Injective (fun i : Fin 5=>nodes A (lowPrefix10 (f i))) := by
    intro i k e
    have es : lowStateAt A (lowPrefix10 (f i))=lowStateAt A (lowPrefix10 (f k)) :=
      lowState_eq_iff.mpr ⟨by simp [off i,off k],e⟩
    have ik := bij.1 ((lowNonterminalState_eq_iff ha (clean1 _) (clean1 _)).mpr es)
    apply Fin.ext
    have t := congrArg Fin.val ik
    change i.val+1=k.val+1 at t
    omega
  let S : Finset K := Finset.univ.image (fun i : Fin 5=>nodes A (lowPrefix10 (f i)))
  have nc : S.card=5 := by simp only [S,Finset.card_image_of_injective _ inj,Finset.card_univ,Fintype.card_fin]
  have dX : (X*P).natDegree≤3 := natDegree_mul_le_of_le (by simp) dP.le
  let V := evalNodes A (-(X*P))+diag (g A) (evalNodes A X)
  have vz (k : Fin 12) (hk : k<j) : V k=0 := by
    by_cases g : g A k=0
    · simp [V,g,pre k hk g]
    · simp [V,fit _ g,mul_comm]
  obtain ⟨R,dR,eq⟩ := degree_three_actual_mat_profile hF (-(X*P)) X
    (by rw [natDegree_neg]; exact dX) (by simp)
  rw [show primitive (-(X*P))=-(primitive (X*P)) from map_neg primitive _] at eq
  change mat A V=_ at eq
  let J := primitive (X*P)
  have dr : (J-P*R).natDegree≤4 :=
    natDegree_sub_le_of_le (primitive_natDegree_le dX) (natDegree_mul_le_of_le dP.le dR)
  have zero : J-P*R=0 := eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ S (fun x hx => by
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hx
    let idx := lowPrefix10 (f k)
    have q := off k
    have z : mat A V idx=0 := causal_mat ha idx V (fun i hi => vz i (hi.trans (pr k)))
    have e := congrFun eq idx
    change mat A V idx=(-J).eval (nodes A idx)+g A idx*R.eval (nodes A idx) at e
    rw [z,eval_neg,←fit _ q] at e
    rw [eval_sub,eval_mul]
    linear_combination e) (by omega)
  have p0 := (first_nonzero_on_forces_head_shape ha hF dP.le pn fit
    ⟨j,fg.first_clean,fg.first_nonzero⟩).1
  exact quadratic_head_not_dvd_own_weighted_primitive dP p0 ⟨R,sub_eq_zero.mp zero⟩


end Ordered
end RKResearch.Certified.Graded.MultiOff
