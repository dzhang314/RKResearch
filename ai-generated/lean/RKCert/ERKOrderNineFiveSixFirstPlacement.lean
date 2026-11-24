module

public import RKCert.ERKOrderNineFiveSixFG
public import RKCert.ERKLowEarlyPrimitive

@[expose] public section

/-! # Physical first-on placement in the remaining quadratic chart -/
namespace RKCert.Paired
open Module Polynomial RKCert.Endpoint
open scoped Classical
variable {K : Type*} [Field K]

/-- If zero and at most two off state nodes are available before a
clean row, the two paid defect tests exclude a nonzero clean clock. -/
theorem first_nonzero_on_at_least_fifth [CharZero K] {A : Fin 12→Fin 12→K}
    (ha : StrictLower A) (hF : zeroSpace A 4=chainSpan A (qdef A) 2)
    {P : K[X]} (fit : ∀ j,qdef A j≠0 → P.eval (nodes A j)=qdef A j)
    {i : Fin 12} (hi : qdef A i=0) (hn : nodes A i≠0)
    (before : ∀ j : Fin 12, j < i → qdef A j = 0 → nodes A j = 0) : 4 ≤ i.val := by
  by_contra! small
  let F := (Finset.univ : Finset (Fin 12)).filter (fun j => j < i ∧ qdef A j ≠ 0)
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
        exact off (e.symm ▸ origin_zeroSpace A ha 2 (qdef_mem A))
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
  let W := diag (qdef A) (evalNodes A R)
  have w4 : mat A W∈zeroSpace A 4 := mat_zeroSpace_charZero A 3
    (chainSpan_le_zeroSpace (qdef_mem A) 1 (chainSpan_iff_polynomial.mpr ⟨R,dr,rfl⟩))
  rw [hF,chainSpan_iff_polynomial] at w4
  obtain ⟨T,_,he⟩ := w4
  have wt : mat A W i=0 := by simpa [hi] using congrFun he i
  have same (j : Fin 12) (hj : j < i) : nodes A j=W j := by
    by_cases h : qdef A j=0
    · simp [W,h,before j hj h]
    · have js : nodes A j∈S := Finset.mem_image.mpr
        ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj,h⟩,rfl⟩
      have eqe := Lagrange.eval_interpolate_at_node y (Set.injOn_id _) js
      change R.eval (nodes A j)=y (nodes A j) at eqe
      change nodes A j=qdef A j*R.eval (nodes A j)
      rw [eqe]
      change nodes A j=qdef A j*(nodes A j/P.eval (nodes A j))
      rw [fit _ h,mul_div_cancel₀ _ h]
  have z := causal_mat ha i (nodes A-W) (fun j hj => sub_eq_zero.mpr (same j hj))
  rw [map_sub,Pi.sub_apply,wt,sub_zero] at z
  change mat A (nodes A) i-(2:K)⁻¹*nodes A i^2=0 at hi
  rw [z,zero_sub,neg_eq_zero] at hi
  exact (mul_ne_zero (inv_ne_zero (by norm_num)) (pow_ne_zero _ hn)) hi

theorem first_prefix_state_ne_terminal
    (i : Fin 10) : lowPrefix10 i≠Fin.last 11 := by
  intro h
  have e := congrArg Fin.val h
  change i.val=11 at e
  omega

theorem first_prefix_clean_value_ne_one {A : Fin 12→Fin 12→K}
    (last : ∀j,qdef A j=0 → nodes A j=1 → j=Fin.last 11)
    (i : Fin 10) (on : qdef A (lowPrefix10 i)=0) : nodes A (lowPrefix10 i)≠1 :=
  fun e => first_prefix_state_ne_terminal i (last _ on e)

section Ordered
variable [LinearOrder K] [IsStrictOrderedRing K]

theorem order9_actual_quadratic_first_on_fifth_or_sixth
    {A : Fin 12→Fin 12→K} {b : Vec K 12}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 9)
    (hM : (onNodes A).card=6) (hN : (supportedNodes A (qdef A)).card=5)
    (hF : zeroSpace A 4=chainSpan A (qdef A) 2)
    {P : K[X]} (dP : P.natDegree=2) (pn : P≠0)
    (fit : ∀ j,qdef A j≠0 → P.eval (nodes A j)=qdef A j)
    (fg : ActualSixOnFG A P) : fg.first.val=4 ∨ fg.first.val=5 := by
  let _ : DecidableEq K := fun _ _ => Classical.propDecidable _
  let j := lowPrefix10 fg.first
  let h := nodes A j
  have pre (i : Fin 12) (hi : i<j) (g : qdef A i=0) : nodes A i=0 := by
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
  have clean1 (i : Fin 10) (hi : qdef A (lowPrefix10 i)=0) : nodes A (lowPrefix10 i)≠1 :=
    first_prefix_clean_value_ne_one last i hi
  have zeroD : qdef A (lowPrefix10 0)=0 := origin_zeroSpace A ha 2 (qdef_mem A)
  have zeroC : nodes A (lowPrefix10 0)=0 := by
    change nodes A (0:Fin 12)=0
    unfold nodes
    exact Finset.sum_eq_zero (fun j _=>ha 0 j (Nat.zero_le _))
  let f (i : Fin 5) : Fin 10 := Fin.castLE (by decide : 6≤10) i.succ
  have pr (i : Fin 5) : f i<fg.first := by
    change i.val+1<fg.first.val
    have := i.isLt
    omega
  have off (i : Fin 5) : qdef A (lowPrefix10 (f i))≠0 := by
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
  let V := evalNodes A (-(X*P))+diag (qdef A) (evalNodes A X)
  have vz (k : Fin 12) (hk : k<j) : V k=0 := by
    by_cases g : qdef A k=0
    · simp [V,g,pre k hk g]
    · simp [V,fit _ g,mul_comm]
  obtain ⟨R,dR,eq⟩ := degree_three_actual_mat_profile hF (-(X*P)) X
    (by rw [natDegree_neg]; exact dX) (by simp)
  rw [map_neg] at eq
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
    change mat A V idx=(-J).eval (nodes A idx)+qdef A idx*R.eval (nodes A idx) at e
    rw [z,eval_neg,←fit _ q] at e
    rw [eval_sub,eval_mul]
    linear_combination e) (by omega)
  have p0 := (first_nonzero_on_forces_head_shape ha hF dP.le pn fit
    ⟨j,fg.first_clean,fg.first_nonzero⟩).1
  exact quadratic_head_not_dvd_own_weighted_primitive dP p0 ⟨R,sub_eq_zero.mp zero⟩

end Ordered
end RKCert.Paired
