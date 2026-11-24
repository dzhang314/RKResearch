module

public import RKCert.ERKOrderNineFiveSixStates

@[expose] public section

/-! # The ten physical prefix states in the five-off/six-on chart

The transpose of the actual reverse row has full aggregate support on
the ten nonterminal states. Causality locates the repeated occurrence
forced by the eleventh-state rank profile, without any graph quotient
or nonlinear stage identification.
-/
namespace RKCert.Paired
open Module Polynomial RKCert.Endpoint
open scoped Classical
variable {K : Type*} [Field K] [CharZero K] {s : ℕ}

/-- All ordinary clean and off aggregates are nonzero for a nontrivial
state-level fifth-grade annihilator that vanishes on the unique endpoint. -/
theorem fifth_profile_annih_full_nonterminal_support {A : Fin s → Fin s → K}
    {w : Vec K s} (hw : w∈annih (treeSpace A 5)) (hW : w∉annih (onOffSpace A))
    (hN : (supportedNodes A (qdef A)).card=5) (hM : (onNodes A).card=6)
    {P : K[X]} (dP : P.natDegree≤2)
    (fit : ∀ i,qdef A i≠0 → P.eval (nodes A i)=qdef A i)
    (hP : ∀ x∈endpointErase (onNodes A) 1,P.eval x≠0)
    (one : (1:K)∈onNodes A) (wend : onWeight A w 1=0) :
    (∀ x∈endpointErase (onNodes A) 1,onWeight A w x≠0) ∧
      (∀ x∈supportedNodes A (qdef A),offWeight A w x≠0) := by
  let S := endpointErase (onNodes A) 1
  let T := supportedNodes A (qdef A)
  have s5 : S.card=5 := by
    have e := Finset.card_erase_add_one one
    change S.card+1=(onNodes A).card at e
    omega
  let f (x : K) := onWeight A w x*P.eval x
  let g (x : K) := offWeight A w x*P.eval x
  have gn (x : K) (hx : x∈T) : P.eval x≠0 := by
    obtain ⟨i,hi,rfl⟩:=mem_supportedNodes.mp hx
    rwa [fit i hi]
  have strip (h : K → K) : (∑x∈onNodes A,onWeight A w x*h x)=∑x∈S,onWeight A w x*h x := by
    have he := Finset.sum_erase_add (onNodes A) (fun x => onWeight A w x*h x) one
    simpa [S,wend] using he.symm
  have extend (a : ∀x∈S,onWeight A w x=0) : ∀x∈onNodes A,onWeight A w x=0 := by
    intro x hx
    by_cases hx' : x=1
    · simpa [hx'] using wend
    · exact a x (Finset.mem_erase.mpr ⟨hx',hx⟩)
  have hp (Q : K[X]) (dQ : Q.natDegree≤5) :
      (∑x∈S,onWeight A w x*Q.eval x)+(∑x∈T,offWeight A w x*Q.eval x)=0 := by
    have h := mem_annih.mp hw _ (evalNodes_mem_treeSpace A Q dQ)
    rwa [row_polynomial_to_weights,strip] at h
  have gf (Q : K[X]) (dQ : Q.natDegree≤3) : ∑x∈T,g x*Q.eval x=0 := by
    have h : diag (qdef A) (evalNodes A Q)∈treeSpace A 5 := by
      have e := pairProfile_mem_E5 A (0:K[X]) Q (by simp) dQ
      have z : evalNodes A (0:K[X])=0 := by ext i; simp
      rwa [z,zero_add] at e
    have e := mem_annih.mp hw _ h
    rw [row_defect_to_off_weights w P Q fit] at e
    simpa only [g,mul_assoc] using e
  have ff (Q : K[X]) (dQ : Q.natDegree≤3) : ∑x∈S,f x*Q.eval x=0 := by
    have h := hp (P*Q) (natDegree_mul_le_of_le dP dQ)
    simp only [eval_mul,←mul_assoc] at h
    change (∑x∈S,f x*Q.eval x)+(∑x∈T,g x*Q.eval x)=0 at h
    rwa [gf Q dQ,add_zero] at h
  have nf : ∃x∈S,f x≠0 := by
    by_contra! h
    have hOn (x : K) (hx : x∈S) : onWeight A w x=0 :=
      (mul_eq_zero.mp (h x hx)).resolve_right (hP x hx)
    have hOff := weight_zero_by_full_interpolation T (offWeight A w) (fun Q dq => by
      have e := hp Q (by change Q.natDegree<(supportedNodes A (qdef A)).card at dq; omega)
      have z : ∑x∈S,onWeight A w x*Q.eval x=0 :=
        Finset.sum_eq_zero (fun x hx=>by rw [hOn x hx,zero_mul])
      rwa [z,zero_add] at e)
    exact hW (row_of_all_weights_zero hOff (extend hOn))
  have ng : ∃x∈T,g x≠0 := by
    by_contra! h
    have hOff (x : K) (hx : x∈T) : offWeight A w x=0 :=
      (mul_eq_zero.mp (h x hx)).resolve_right (gn x hx)
    have hOn := weight_zero_by_full_interpolation S (onWeight A w) (fun Q dq => by
      have e := hp Q (by omega)
      have z : ∑x∈T,offWeight A w x*Q.eval x=0 :=
        Finset.sum_eq_zero (fun x hx=>by rw [hOff x hx,zero_mul])
      rwa [z,add_zero] at e)
    exact hW (row_of_all_weights_zero hOff (extend hOn))
  exact ⟨fun x hx hz => weight_full_support_of_five S f s5 ff nf x hx (by simp [f,hz]),
    fun x hx hz => weight_full_support_of_five T g hN gf ng x hx (by simp [g,hz])⟩

omit [CharZero K] in
theorem onWeight_one_of_unique_zero {A : Fin (s+1) → Fin (s+1) → K} (w : Vec K (s+1))
    (hw : w (Fin.last s)=0) (hu : ∀i,qdef A i=0 → nodes A i=1 → i=Fin.last s) :
    onWeight A w 1=0 := by
  unfold onWeight
  apply Finset.sum_eq_zero
  intro i _
  by_cases h : qdef A i=0 ∧ nodes A i=1
  · rw [ite_eq_left h,hu i h.1 h.2,hw]
  · simp [h]

abbrev LowNonterminalState (A : Fin s → Fin s → K) :=
  Sum (↥(endpointErase (onNodes A) 1)) (↥(supportedNodes A (qdef A)))

noncomputable def lowNonterminalStateAt {A : Fin (s+1) → Fin (s+1) → K}
    (ha : StrictLower A) (i : Fin (s+1)) : LowNonterminalState A :=
  if h : qdef A i≠0 then Sum.inr ⟨nodes A i,mem_supportedNodes.mpr ⟨i,h,rfl⟩⟩
  else if hc : nodes A i≠1 then Sum.inl ⟨nodes A i,
    Finset.mem_erase.mpr ⟨hc,mem_onNodes.mpr ⟨i,not_not.mp h,rfl⟩⟩⟩
  else Sum.inl ⟨0,Finset.mem_erase.mpr ⟨zero_ne_one,zero_mem_onNodes ha⟩⟩

theorem earlier_nonterminal_states_surjective {A : Fin (s+1) → Fin (s+1) → K}
    (ha : StrictLower A) {w : Vec K (s+1)} (j : Fin (s+1))
    (hW : ∀ i : Fin (s+1), j ≤ i → w i=0)
    (hOn : ∀x∈endpointErase (onNodes A) 1,onWeight A w x≠0)
    (hOff : ∀x∈supportedNodes A (qdef A),offWeight A w x≠0) :
    Function.Surjective (fun i : Fin j.val => lowNonterminalStateAt ha (Fin.castLE j.isLt.le i)) := by
  intro z
  rcases z with a|a
  · obtain ⟨i,hi,hg,hc⟩ := stage_before_of_tagged_weight_nonzero w (nodes A) j hW
      (fun i => qdef A i=0) a.val (hOn a.val a.property)
    refine ⟨⟨i.val,hi⟩,?_⟩
    change lowNonterminalStateAt ha i=Sum.inl a
    have hn := (Finset.mem_erase.mp a.property).1
    simp [lowNonterminalStateAt,hg,hc,hn]
  · obtain ⟨i,hi,hg,hc⟩ := stage_before_of_tagged_weight_nonzero w (nodes A) j hW
      (fun i => qdef A i≠0) a.val (hOff a.val a.property)
    refine ⟨⟨i.val,hi⟩,?_⟩
    change lowNonterminalStateAt ha i=Sum.inr a
    simp [lowNonterminalStateAt,hg,hc]

section Ordered
variable {L : Type*} [Field L] [LinearOrder L] [IsStrictOrderedRing L]

/-- In the remaining six-on chart, the first ten physical stages
represent every nonterminal state exactly once. The later repeated
occurrence is exactly index ten. -/
theorem order9_five_six_ten_distinct_prefix
    {A : Fin 12 → Fin 12 → L} {b : Vec L 12} (ha : StrictLower A)
    (ho : HasTreeOrderAtLeast A b 9)
    (hN : (supportedNodes A (qdef A)).card=5) (hM : (onNodes A).card=6) :
    Function.Bijective (fun i : Fin 10 => lowNonterminalStateAt ha (Fin.castLE (by decide) i)) ∧
      (∃ i : Fin 12,i<(10:Fin 12) ∧ lowStateAt A i=lowStateAt A (10:Fin 12) ∧
        ∃ a : L,a≠0 ∧ orderAdjoint A b 1=a • (Pi.single i 1-Pi.single (10:Fin 12) 1)) ∧
      (∀x∈endpointErase (onNodes A) 1,onWeight A (transMat A (orderAdjoint A b 1)) x≠0) ∧
      (∀x∈supportedNodes A (qdef A),offWeight A (transMat A (orderAdjoint A b 1)) x≠0) := by
  let _ : DecidableEq L := fun _ _ => Classical.propDecidable _
  obtain ⟨_,h3,h4,_,_,_,_,_⟩ := order9_twelve_stage_chart ha ho
  obtain ⟨P,dP,_,_,hF,fit⟩ := two_curve_head h3 h4 (by omega)
  obtain ⟨_,eq6,_,hi,hc,_,hu⟩ := order9_five_six_stage_chart ha ho hN hM fit
  obtain ⟨_,pn⟩ := order9_five_six_remainder ha ho hN hM hF P dP fit
  obtain ⟨i,j,hij,hjl,hs,a,an,hr,hw0⟩ := order9_five_six_reverse_contrast ha ho hN hM fit
  let r := orderAdjoint A b 1
  let w := transMat A r
  have hr6 : r∈annih (treeSpace A 6) := orderAdjoint_annih ho (by decide)
  have hw5 : w∈annih (treeSpace A 5) := transMat_mem_annih_pred hr6
  have wcut (k : Fin 12) (hk : j≤k) : w k=0 := by
    change transMat A (orderAdjoint A b 1) k=0
    rw [hr,map_smul,Pi.smul_apply,smul_eq_mul,map_sub,
      transMat_single_incoming_row,transMat_single_incoming_row,Pi.sub_apply,
      ha i k (hij.le.trans hk),ha j k hk,sub_self,mul_zero]
  have rj : r j=-a := by
    change orderAdjoint A b 1 j=-a
    rw [hr]
    simp [ne_of_gt hij]
  have rn : r≠0 := fun e => neg_ne_zero.mpr an (rj.symm.trans (by rw [e]; rfl))
  have dn : finrank L (annih (treeSpace A 6))=1 := by
    have e := finrank_add_annih_eq (treeSpace A 6)
    rw [eq6,onOffSpace_rank,hM,hN] at e
    rw [eq6]
    omega
  have wstate : w∉annih (onOffSpace A) := by
    intro e
    rw [←eq6] at e
    have sp : Submodule.span L {r}=annih (treeSpace A 6) :=
      Submodule.eq_of_le_of_finrank_le ((Submodule.span_singleton_le_iff_mem ..).mpr hr6)
        (by rw [dn,finrank_span_singleton rn])
    rw [←sp] at e
    obtain ⟨z,hz⟩ := Submodule.mem_span_singleton.mp e
    have ex := congrFun hz j
    change z*r j=w j at ex
    rw [rj,wcut j le_rfl] at ex
    have z0 := (mul_eq_zero.mp ex).resolve_right (neg_ne_zero.mpr an)
    rw [z0,zero_smul] at hz
    exact hw0 hz.symm
  have one : (1:L)∈onNodes A := mem_onNodes.mpr ⟨_,hi,hc⟩
  have w1 := onWeight_one_of_unique_zero w (wcut _ hjl.le) hu
  obtain ⟨hOn,hOff⟩ := fifth_profile_annih_full_nonterminal_support hw5 wstate hN hM dP fit pn one w1
  have surj := earlier_nonterminal_states_surjective ha j wcut hOn hOff
  have card : Fintype.card (LowNonterminalState A)=10 := by
    have t := Finset.card_erase_add_one one
    change (endpointErase (onNodes A) (1:L)).card+1=(onNodes A).card at t
    rw [Fintype.card_sum,Fintype.card_coe,Fintype.card_coe]
    omega
  have bound := Fintype.card_le_of_surjective _ surj
  rw [card,Fintype.card_fin] at bound
  have ej : j=(10:Fin 12) := by
    change j.val<11 at hjl
    exact Fin.ext (by change j.val=10; omega)
  subst j
  have surj' : Function.Surjective (fun i : Fin 10 => lowNonterminalStateAt ha (Fin.castLE (by decide) i)) := surj
  exact ⟨(Fintype.bijective_iff_surjective_and_card _).mpr ⟨surj',by rw [Fintype.card_fin,card]⟩,
    ⟨i,hij,hs,a,an,hr⟩,hOn,hOff⟩

end Ordered
end RKCert.Paired
