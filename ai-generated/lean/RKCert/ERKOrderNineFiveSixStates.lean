module

public import RKCert.ERKOrderNineSixSix
public import RKCert.ERKOrderNineLatePrefixRanks

@[expose] public section

/-! # Exact physical state spaces of the remaining five-off/six-on branch

At grade five the terminal singleton is already part of the exact
polynomial profile, and grade six is the entire eleven-state space.
Its adjoint is a nonzero contrast of two distinct physical rows.
-/
namespace RKCert.Paired
open Module Polynomial RKCert.Endpoint
open scoped Classical
variable {K : Type*} [Field K] [CharZero K]
variable {A : Fin 12 → Fin 12 → K} {b : Vec K 12}

/-- The rank-five polynomial profile and rank-six state span follow
from the actual order conditions, not from identifying repeated stages. -/
theorem order9_five_six_stage_chart (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 9)
    (hN : (supportedNodes A (qdef A)).card=5) (hM : (onNodes A).card=6)
    {P : K[X]} (fit : ∀ i,qdef A i≠0 → P.eval (nodes A i)=qdef A i) :
    gradeFiveStateSpace A=treeSpace A 5 ∧ treeSpace A 6=onOffSpace A ∧
      backSeed1 A b=0 ∧ qdef A (Fin.last 11)=0 ∧ nodes A (Fin.last 11)=1 ∧
      Pi.single (Fin.last 11) 1∈treeSpace A 5 ∧
      (∀ j,qdef A j=0 → nodes A j=1 → j=Fin.last 11) := by
  obtain ⟨hb,_,_,_,_,_,cap5,cap6⟩ := order9_twelve_stage_chart ha ho
  have r5 := gradeFiveState_rank hM.ge (by omega : 4≤(supportedNodes A (qdef A)).card)
  have eq5 : gradeFiveStateSpace A=treeSpace A 5 :=
    Submodule.eq_of_le_of_finrank_le (gradeFiveStateSpace_le A) (by omega)
  have f5 : finrank K (treeSpace A 5)=10 := by rw [←eq5,r5]
  obtain ⟨D1,hc,he,_,_,_⟩ := order9_rank_five_full ha ho f5
  have state5 : treeSpace A 5≤onOffSpace A := eq5 ▸ gradeFive_profiles_state_valued fit
  have hoff : ∀ x∈supportedNodes A (qdef A), offWeight A b x=0 :=
    fun x hx => offWeight_eq_zero_from_head ho P fit (by omega) x hx
  have hi := on_of_state_single (state5 he) hb hoff
  obtain ⟨z,hz⟩ : Pi.single (Fin.last 11) 1∈gradeFiveStateSpace A := eq5 ▸ he
  rw [gradeFiveStateMap_eq_eval] at hz
  have hu (j : Fin 12) (hj : qdef A j=0) (hj' : nodes A j=1) : j=Fin.last 11 :=
    single_profile_on_unique hz hi hc j hj hj'
  let W := treeSpace A 5 ⊔ (treeSpace A 5).map (diag (nodes A))
  have hW : W≤onOffSpace A := sup_le state5 (by
    rintro _ ⟨v,hv,rfl⟩
    exact onOffSpace_diag (state5 hv))
  have leW : treeSpace A 5≤W := le_sup_left
  have wLt : treeSpace A 5<W := lt_of_le_of_ne leW (by
    intro e
    exact order9_treeSpace_five_not_clock_invariant ha ho
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

/-- The exact physical adjoint spans the one-dimensional duplicate
state contrast. Its transpose image is nonzero by the actual ERK
row-surgery obstruction for tight tableaux. -/
theorem order9_five_six_reverse_contrast (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 9)
    (hN : (supportedNodes A (qdef A)).card=5) (hM : (onNodes A).card=6)
    {P : K[X]} (fit : ∀ i,qdef A i≠0 → P.eval (nodes A i)=qdef A i) :
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
  let v : Vec K 12 := Pi.single i 1-Pi.single j 1
  have hv : v∈annih (treeSpace A 6) := by
    apply mem_annih.mpr
    intro w hw
    change row (Pi.single i 1-Pi.single j 1) w=0
    rw [row_sub_col,row_single_left_eq_coord,row_single_left_eq_coord]
    exact sub_eq_zero.mpr (onOffSpace_eq_at_states hs (eq6 ▸ hw))
  have vn : v≠0 := by
    intro e
    simpa [v,ne_of_lt hl] using congrFun e i
  have dr : finrank K (annih (treeSpace A 6))=1 := by
    have e := finrank_add_annih_eq (treeSpace A 6)
    rw [eq6,onOffSpace_rank,hM,hN] at e
    rw [eq6]
    omega
  have eq : Submodule.span K {v}=annih (treeSpace A 6) :=
    Submodule.eq_of_le_of_finrank_le ((Submodule.span_singleton_le_iff_mem ..).mpr hv)
      (by rw [dr,finrank_span_singleton vn])
  have hAdj := orderAdjoint_annih ho (j:=6) (k:=1) (by decide)
  rw [←eq] at hAdj
  have nAdj : orderAdjoint A b 1≠0 := by
    rw [orderAdjoint_one_eq_backward_two D1 (by norm_num)]
    exact smul_ne_zero (neg_ne_zero.mpr (inv_ne_zero (by norm_num)))
      (backSeed2_ne_zero_of_budget ha ho (by decide))
  obtain ⟨a,ha'⟩ := Submodule.mem_span_singleton.mp hAdj
  have an : a≠0 := by intro e; rw [e,zero_smul] at ha'; exact nAdj ha'.symm
  refine ⟨i,j,hl,hj,hs,a,an,ha'.symm,?_⟩
  intro e
  rw [←ha',map_smul] at e
  have e' := (smul_eq_zero.mp e).resolve_left an
  apply no_identical_rows_at_uniform_floor ha ho (by decide) hl
  intro k
  change transMat A (Pi.single i 1-Pi.single j 1)=0 at e'
  rw [map_sub,transMat_single_incoming_row,transMat_single_incoming_row] at e'
  exact congrFun (sub_eq_zero.mp e') k

section Ordered
variable [LinearOrder K] [IsStrictOrderedRing K]

omit [CharZero K] in
/-- The nonzero remainder coefficient and nonzero head on all five
nonterminal clean features, derived from the true terminal singleton. -/
theorem order9_five_six_remainder (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 9)
    (hN : (supportedNodes A (qdef A)).card=5) (hM : (onNodes A).card=6)
    (hF : zeroSpace A 4=chainSpan A (qdef A) 2) (P : K[X]) (dP : P.natDegree≤2)
    (fit : ∀ i,qdef A i≠0 → P.eval (nodes A i)=qdef A i) :
    (∃ k : K, k≠0 ∧ P∣nodalHull (endpointErase (onNodes A) 1) -
        C k*nodalHull (supportedNodes A (qdef A))) ∧
      ∀ x∈endpointErase (onNodes A) 1,P.eval x≠0 := by
  let _ : DecidableEq K := fun _ _ => Classical.propDecidable _
  obtain ⟨e5,_,_,hi,hc,he,hu⟩ := order9_five_six_stage_chart ha ho hN hM fit
  let i := Fin.last 11
  have h1 : (1:K)∈onNodes A := mem_onNodes.mpr ⟨i,hi,hc⟩
  let S := endpointErase (onNodes A) 1
  let T := supportedNodes A (qdef A)
  let F := nodalHull S
  let H := nodalHull T
  have s5 : S.card=5 := by
    have e := Finset.card_erase_add_one h1
    change S.card+1=(onNodes A).card at e
    omega
  obtain ⟨z,hz⟩ : Pi.single i 1∈gradeFiveStateSpace A := e5 ▸ he
  rw [gradeFiveStateMap_eq_eval] at hz
  let Q := ofFn 6 z.1
  let R := ofFn 4 z.2
  change evalNodes A Q+diag (qdef A) (evalNodes A R)=Pi.single i 1 at hz
  have dq : Q.natDegree≤5 := Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) _)
  have dr : R.natDegree≤3 := Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) _)
  obtain ⟨a,ea⟩ := polynomial_scalar_hull S Q (dq.trans_eq s5.symm) (fun x hx => by
    obtain ⟨hn,hx'⟩ := Finset.mem_erase.mp hx
    obtain ⟨j,hj,rfl⟩ := mem_onNodes.mp hx'
    have ne : j≠i := fun e => hn (e.symm ▸ hc)
    simpa [ne] using profile_on_eval Q R hz hj)
  obtain ⟨c,ec⟩ := polynomial_scalar_hull T (Q+P*R)
    ((natDegree_add_le_of_degree_le dq (natDegree_mul_le_of_le dP dr)).trans_eq hN.symm)
    (fun x hx=>by
      obtain ⟨j,hj,rfl⟩ := mem_supportedNodes.mp hx
      have ne : j≠i := fun e => hj (e.symm ▸ hi)
      simpa [ne] using profile_off_eval hz fit hj)
  have an : a≠0 := by
    intro e
    have h := profile_on_eval Q R hz hi
    change Q.eval (nodes A i)=(Pi.single i 1 : Vec K 12) i at h
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
    have off : ∀x∈supportedNodes A (qdef A), offWeight A b x=0 :=
      fun x hx => offWeight_eq_zero_from_head ho P fit (by omega) x hx
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
  have hT : x∈T := by by_contra hn; exact nodalHull_eval_ne_zero_of_notMem hn hh
  obtain ⟨i',hi',he''⟩ := mem_supportedNodes.mp hT
  exact hi' ((fit _ hi').symm.trans (he''.symm ▸ he'))

end Ordered
end RKCert.Paired
