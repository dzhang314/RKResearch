module
public import RKCert.ReviewedNative.OrderNineCohortGeometry

@[expose] public section

/-! # Actual five-six branch: full grades, unique clean terminal and common-head remainder -/
namespace RKResearch.Certified.Graded.MultiOff
open RKResearch Module Polynomial OneOff Reverse RKCert.Endpoint
open scoped Matrix Classical
variable {K : Type*} [Field K] [CharZero K] {A : Matrix (Fin 12) (Fin 12) K} {b : Fin 12→K}

theorem order9_five_six_stage_chart (ha : ∀i j,i≤j → A i j=0) (ho : HasOrder A b 9)
    (hN : (offKnots A).card=5) (hM : (cleanKnots A).card=6)
    {P : K[X]} (fit : ∀ i,g A i≠0 → P.eval (nodes A i)=g A i) :
    gradeFiveStateSpace A=treeSpace A 5 ∧ treeSpace A 6=onOffSpace A ∧
      firstSeed A b=0 ∧ g A (Fin.last 11)=0 ∧ nodes A (Fin.last 11)=1 ∧
      Pi.single (Fin.last 11) 1∈treeSpace A 5 ∧
      (∀ j,g A j=0 → nodes A j=1 → j=Fin.last 11) := by
  have cap5 := order9_grade_five_upper ha ho
  have cap6 := order9_grade_six_upper ha ho
  have r5 := gradeFiveState_rank hM.ge (by omega : 4≤(offKnots A).card)
  have eq5 : gradeFiveStateSpace A=treeSpace A 5 :=
    Submodule.eq_of_le_of_finrank_le (gradeFiveStateSpace_le A) (by omega)
  have f5 : finrank K (treeSpace A 5)=10 := by rw [←eq5,r5]
  obtain ⟨hb,hc,e,_⟩ := order9_rank_five_full_terminal ha ho f5
  have D1 := (Reverse.orderNine_rank_five_full ha ho f5).1
  have he : Pi.single (Fin.last 11) 1∈treeSpace A 5 := by rwa [←coordinate_as_single]
  have state5 : treeSpace A 5≤onOffSpace A := eq5 ▸ gradeFive_profiles_state_valued fit
  have hoff : ∀ x∈offKnots A, offMass A b x=0 :=
    fun x hx => offMass_zero_of_head ho fit (by omega) x hx
  have hi := on_of_state_single (state5 he) hb hoff
  obtain ⟨z,hz⟩ : Pi.single (Fin.last 11) 1∈gradeFiveStateSpace A := eq5 ▸ he
  rw [gradeFiveStateMap_eq_eval] at hz
  have hu (j : Fin 12) (hj : g A j=0) (hj' : nodes A j=1) : j=Fin.last 11 :=
    single_profile_on_unique hz hi hc j hj hj'
  let W := treeSpace A 5 ⊔ (treeSpace A 5).map (diag (nodes A))
  have hW : W≤onOffSpace A := sup_le state5 (by
    rintro _ ⟨v,hv,rfl⟩
    exact onOffSpace_diag (state5 hv))
  have leW : treeSpace A 5≤W := le_sup_left
  have wLt : treeSpace A 5<W := lt_of_le_of_ne leW (by
    intro e
    exact grade_five_not_stable ha ho
      ((show (treeSpace A 5).map (diag (nodes A))≤W from le_sup_right).trans e.ge))
  have wRank := Submodule.finrank_lt_finrank_of_lt wLt
  have stateRank : finrank K (onOffSpace A)=11 := by rw [onOffSpace_rank,hM,hN]
  have eW : W=onOffSpace A := Submodule.eq_of_le_of_finrank_le hW (by omega)
  have w6 : W≤treeSpace A 6 := sup_le (treeSpace_mono A (by decide)) (by
    rintro _ ⟨v,hv,rfl⟩
    exact diag_treeSpace A 5 hv)
  have h61 : onOffSpace A≤treeSpace A 6 := eW ▸ w6
  have eq6 := Submodule.eq_of_le_of_finrank_le h61 (by omega)
  exact ⟨eq5,eq6.symm,D1,hi,hc,he,hu⟩

theorem order9_five_six_reverse_contrast (ha : ∀i j,i≤j → A i j=0) (ho : HasOrder A b 9)
    (hN : (offKnots A).card=5) (hM : (cleanKnots A).card=6)
    {P : K[X]} (fit : ∀ i,g A i≠0 → P.eval (nodes A i)=g A i) :
    ∃ i j : Fin 12, i<j ∧ j<Fin.last 11 ∧ lowStateAt A i=lowStateAt A j ∧
      ∃ a : K, a≠0 ∧
        orderAdjoint A b 1=a • (Pi.single i 1-Pi.single j 1) ∧ transMat A (orderAdjoint A b 1)≠0 := by
  obtain ⟨_,eq6,D1,_,_,he,_⟩ := order9_five_six_stage_chart ha ho hN hM fit
  let f := fun i : Fin 12 => lowStateAt A i
  have fn : ¬ Function.Injective f := by
    intro h
    have e := Fintype.card_le_of_injective f h
    rw [Fintype.card_fin,lowState_card,hM,hN] at e
    omega
  obtain ⟨x,y,heq,hxy⟩ := Function.not_injective_iff.mp fn
  obtain ⟨i,j,hl,hs⟩ : ∃ i j : Fin 12, i<j ∧ lowStateAt A i=lowStateAt A j := by
    rcases lt_or_gt_of_ne hxy with hl|hl
    · exact ⟨x,y,hl,heq⟩
    · exact ⟨y,x,hl,heq.symm⟩
  have hj : j<Fin.last 11 := by
    apply lt_of_le_of_ne (Fin.le_last j)
    intro h
    subst j
    have e := onOffSpace_eq_at_states hs (eq6 ▸ (treeSpace_mono A (by decide : 5≤6) he))
    have hn := ne_of_lt hl
    change i≠(11:Fin 12) at hn
    simp [hn] at e
  have dim : finrank K (treeSpace A 6)=11 := by rw [eq6,onOffSpace_rank,hM,hN]
  exact ⟨i,j,hl,hj,hs,order9_contrast_of_pair ha ho D1 dim hl
    (fun w hw=>onOffSpace_eq_at_states hs (eq6 ▸ hw))⟩

variable [LinearOrder K] [IsStrictOrderedRing K]

omit [CharZero K] in
theorem order9_five_six_remainder (ha : ∀i j,i≤j → A i j=0) (ho : HasOrder A b 9)
    (hN : (offKnots A).card=5) (hM : (cleanKnots A).card=6)
    (hF : zeroSpace A 4=band A 2) (P : K[X]) (dP : P.natDegree≤2)
    (fit : ∀ i,g A i≠0 → P.eval (nodes A i)=g A i) :
    (∃ k : K, k≠0 ∧ P∣nodalHull (RKCert.Paired.endpointErase (cleanKnots A) 1) -
        C k*nodalHull (offKnots A)) ∧
      ∀ x∈RKCert.Paired.endpointErase (cleanKnots A) 1,P.eval x≠0 := by
  let _ : DecidableEq K := fun _ _ => Classical.propDecidable _
  obtain ⟨e5,_,_,hi,hc,he,hu⟩ := order9_five_six_stage_chart ha ho hN hM fit
  let i := Fin.last 11
  have h1 : (1:K)∈cleanKnots A := mem_cleanKnots.mpr ⟨i,hi,hc⟩
  let S := RKCert.Paired.endpointErase (cleanKnots A) 1
  let T := offKnots A
  let F := nodalHull S
  let H := nodalHull T
  have s5 : S.card=5 := by
    have e := Finset.card_erase_add_one h1
    change S.card+1=(cleanKnots A).card at e
    omega
  obtain ⟨z,hz⟩ : Pi.single i 1∈gradeFiveStateSpace A := e5 ▸ he
  rw [gradeFiveStateMap_eq_eval] at hz
  let Q := ofFn 6 z.1
  let R := ofFn 4 z.2
  change evalNodes A Q+diag (g A) (evalNodes A R)=Pi.single i 1 at hz
  have dq : Q.natDegree≤5 := Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) _)
  have dr : R.natDegree≤3 := Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) _)
  obtain ⟨a,ea⟩ := RKCert.Paired.polynomial_scalar_hull S Q (dq.trans_eq s5.symm) (fun x hx => by
    obtain ⟨hn,hx'⟩ := Finset.mem_erase.mp hx
    obtain ⟨j,hj,rfl⟩ := mem_cleanKnots.mp hx'
    have ne : j≠i := fun e => hn (e.symm ▸ hc)
    simpa [ne] using profile_on_eval Q R hz hj)
  obtain ⟨c,ec⟩ := RKCert.Paired.polynomial_scalar_hull T (Q+P*R)
    ((natDegree_add_le_of_degree_le dq (natDegree_mul_le_of_le dP dr)).trans_eq hN.symm)
    (fun x hx=>by
      obtain ⟨j,hj,rfl⟩ := mem_offKnots.mp hx
      have ne : j≠i := fun e => hj (e.symm ▸ hi)
      simpa [ne] using profile_off_eval hz fit hj)
  have an : a≠0 := by
    intro e
    have h := profile_on_eval Q R hz hi
    change Q.eval (nodes A i)=(Pi.single i 1 : (Fin 12→K)) i at h
    simp [ea,e] at h
  have qd : Q.natDegree=5 := by rw [ea,natDegree_C_mul an,natDegree_nodalHull,s5]
  have cn : c≠0 := by
    intro e
    have eq : Q=-(P*R) := by have t := ec; simp [e] at t; linear_combination t
    have d2 : P.natDegree=2 := by
      by_contra! h
      have e' := natDegree_mul_le_of_le (show P.natDegree≤1 by omega) dr
      rw [eq,natDegree_neg] at qd
      omega
    have hdiv : P∣F := ⟨-(C a⁻¹*R),by
      calc F=C a⁻¹*Q := by rw [ea,←mul_assoc,←map_mul,inv_mul_cancel₀ an,map_one,one_mul]
      _=P*-(C a⁻¹*R) := by rw [eq]; ring⟩
    have off : ∀x∈offKnots A, offMass A b x=0 :=
      fun x hx => offMass_zero_of_head ho fit (by omega) x hx
    obtain ⟨l,hp⟩ := order9_six_on_pencil ha ho hM h1 off
    exact six_on_pencil_divisor_impossible ha hF hM h1 hu P d2 fit hdiv hp
  have rem : F-C (c/a)*H=P*(-(C a⁻¹*R)) := by
    have ea' : Q=C a*F := ea
    have ec' : Q+P*R=C c*H := ec
    have ea'' : F=C a⁻¹*Q := by rw [ea',←mul_assoc,←map_mul,inv_mul_cancel₀ an,map_one,one_mul]
    rw [ea'',div_eq_mul_inv,map_mul]
    linear_combination C a⁻¹*ec'
  refine ⟨⟨c/a,div_ne_zero cn an,⟨_,rem⟩⟩,?_⟩
  intro x hx he'
  have hxS : x∈S := hx
  have eval0 : (nodalHull S).eval x=0 := nodalHull_eval_of_mem hxS
  have h : (Q+P*R).eval x=0 := by
    rw [eval_add,ea,eval_mul,eval0,mul_zero,eval_mul,he',zero_mul,zero_add]
  have hh : H.eval x=0 := by
    rw [ec,eval_mul,eval_C] at h
    exact (mul_eq_zero.mp h).resolve_left cn
  have hT : x∈T := by by_contra hn; exact RKCert.Paired.nodalHull_eval_ne_zero_of_notMem hn hh
  obtain ⟨i',hi',he''⟩ := mem_offKnots.mp hT
  exact hi' ((fit _ hi').symm.trans (he''.symm ▸ he'))
end RKResearch.Certified.Graded.MultiOff
