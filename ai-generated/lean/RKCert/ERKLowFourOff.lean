module

public import RKCert.ERKLowStates

@[expose] public section

/-! # The four-off branch at order nine

The excluded endpoint on a five-node on rule follows from a rational
four-row moment identity. No sign assumption or analysis is needed.
-/
namespace RKCert.Paired
open Module Polynomial
open scoped Classical

variable {K : Type*} [Field K] [CharZero K] {s : ℕ}

set_option maxHeartbeats 600000 in
theorem cubic_beta_moments_top_zero (a : Fin 4 → K)
    (h : ∀ i : Fin 4,
      (∑ j : Fin 4, a j / ((i.val+j.val+3:ℕ):K)) -
        (∑ j : Fin 4, a j / ((i.val+j.val+2:ℕ):K))=0) : a 3=0 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  norm_num [Fin.sum_univ_succ] at h0 h1 h2 h3
  linear_combination 2520*h0 - 22680*h1 + 52920*h2 - 35280*h3

/-- There is no fifth on node at one if zero is already an on node and
five on nodes carry the exact degree-eight quadrature. -/
theorem one_not_on_of_five {A : Fin (s+1) → Fin (s+1) → K} {b : Vec K (s+1)}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 9)
    (hM : (onNodes A).card=5)
    (hoff : ∀ x∈supportedNodes A (qdef A), offWeight A b x=0) :
    (1:K)∉onNodes A := by
  intro h1
  let T := (onNodes A).erase 1
  have h0 : (0:K)∈T := Finset.mem_erase.mpr ⟨zero_ne_one,zero_mem_onNodes ha⟩
  let S := T.erase 0
  have hT : T.card+1=(onNodes A).card := Finset.card_erase_add_one h1
  have hS : S.card+1=T.card := Finset.card_erase_add_one h0
  let Q : K[X] := ∏ a∈S, (X-C a)
  have hm : Q.Monic := Polynomial.monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _
  have hd : Q.natDegree=3 := by
    have he : Q.natDegree=S.card := by simp [Q]
    omega
  let P := (X^2-X)*Q
  have hroots (a : K) (ha : a∈onNodes A) : P.eval a=0 := by
    by_cases h : a=0 ∨ a=1
    · rcases h with rfl|rfl <;> simp [P]
    · have hm : a∈S := Finset.mem_erase.mpr ⟨fun h' => h (Or.inl h'),
          Finset.mem_erase.mpr ⟨fun h' => h (Or.inr h'),ha⟩⟩
      have hz : Q.eval a=0 := by
        rw [show Q.eval a = ∏ x∈S,(X-C x : K[X]).eval a by simp [Q,Polynomial.eval_prod]]
        exact Finset.prod_eq_zero hm (by simp)
      simp [P,hz]
  have he (k : ℕ) :
      probe A b k (evalNodes A P) =
        probe A b (k+2) (evalNodes A Q) - probe A b (k+1) (evalNodes A Q) := by
    simp only [probe,row_apply,evalNodes_apply,←Finset.sum_sub_distrib,P,eval_mul,eval_sub,eval_pow,eval_X]
    apply Finset.sum_congr rfl
    intro i _
    simp only [pow_add,pow_one]
    ring
  have hh (i : Fin 4) :
      (∑ j : Fin 4, Q.coeff j.val / ((i.val+j.val+3:ℕ):K)) -
        (∑ j : Fin 4, Q.coeff j.val / ((i.val+j.val+2:ℕ):K))=0 := by
    have h := probes_zero_of_on_roots hoff P hroots i.val
    rw [he,evalNodes_eq_polyEval A Q hd.le,probe_polyEval ho (by have := i.isLt; omega),
      probe_polyEval ho (by have := i.isLt; omega)] at h
    have e (j : Fin 4) : i.val+2+j.val+1=i.val+j.val+3 := by omega
    have e' (j : Fin 4) : i.val+1+j.val+1=i.val+j.val+2 := by omega
    simpa only [e,e'] using h
  have hz := cubic_beta_moments_top_zero _ hh
  have hc : Q.coeff 3=1 := by
    rw [←hd, ←Polynomial.leadingCoeff, hm.leadingCoeff]
  exact (one_ne_zero : (1:K)≠0) (hc.symm.trans hz)

omit [CharZero K] in
theorem onOffSpace_adjoin_single_clock {A : Fin s → Fin s → K} (i : Fin s) :
    let W := onOffSpace A ⊔ Submodule.span K {Pi.single i 1}
    W.map (diag (nodes A)) ≤ W := by
  dsimp only
  apply Submodule.map_le_iff_le_comap.mpr
  intro v hv
  obtain ⟨x,hx,y,hy,rfl⟩ := Submodule.mem_sup.mp hv
  obtain ⟨k,rfl⟩ := Submodule.mem_span_singleton.mp hy
  have hd : diag (nodes A) (Pi.single i 1) = nodes A i • Pi.single i 1 := by
    ext j
    by_cases h : j=i <;> simp [h]
  change diag (nodes A) (x+k • Pi.single i 1) ∈ onOffSpace A ⊔ Submodule.span K {Pi.single i 1}
  rw [map_add,map_smul,hd,smul_smul]
  exact Submodule.mem_sup.mpr ⟨_,onOffSpace_diag hx,_,
    (Submodule.span K {Pi.single i 1}).smul_mem _ (Submodule.mem_span_singleton_self _),rfl⟩

/-- The actual four-off branch of the twelve-stage order-nine chart is
impossible, including all repeated-state configurations. -/
theorem order9_no_four_off_nodes {A : Fin 12 → Fin 12 → K} {b : Vec K 12}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 9) :
    (supportedNodes A (qdef A)).card≠4 := by
  intro hN
  obtain ⟨hb,h3,h4,_,_,he5lo,he5hi,_⟩ := order9_twelve_stage_chart ha ho
  obtain ⟨P,_,_,_,_,hP⟩ := two_curve_head h3 h4 (by omega)
  have hoff : ∀ x∈supportedNodes A (qdef A), offWeight A b x=0 :=
    fun x hx => offWeight_eq_zero_from_head ho P hP (by omega) x hx
  have hMlo : 5 ≤ (onNodes A).card := five_on_of_aggregate_zero (s:=11) ha ho (by decide) hoff
  have hMhi := order9_on_count_le_six ha ho (by omega) P hP hoff
  have hLE := onOffSpace_le_E5 hP hMhi hN.le
  have hR := onOffSpace_rank A
  apply order9_treeSpace_five_not_clock_invariant ha ho
  by_cases hE : finrank K (treeSpace A 5) ≤ finrank K (onOffSpace A)
  · rw [←Submodule.eq_of_le_of_finrank_le hLE hE]
    apply Submodule.map_le_iff_le_comap.mpr
    intro v hv
    exact onOffSpace_diag hv
  · have hM : (onNodes A).card=5 := by omega
    have hE5 : finrank K (treeSpace A 5)=10 := by omega
    obtain ⟨_,hc,hi,_,_,_⟩ := order9_rank_five_full ha ho hE5
    let i := Fin.last 11
    have hout : Pi.single i 1 ∉ onOffSpace A := by
      intro hw
      have hd := on_of_state_single hw hb hoff
      exact one_not_on_of_five (s:=11) ha ho hM hoff (mem_onNodes.mpr ⟨i,hd,hc⟩)
    have hs := sup_singleton_eq_of_rank hLE hi hout (by omega)
    rw [hs]
    exact onOffSpace_adjoin_single_clock i

/-- In either middle off-count branch at order eight, the on rule has
exactly five distinct nodes. For four off nodes, six on states would
already fill ten columns of E5 by separate interpolation. -/
theorem order8_five_on_of_middle_offs {A : Fin 10 → Fin 10 → K} {b : Vec K 10}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 8)
    (hN : (supportedNodes A (qdef A)).card=4 ∨ (supportedNodes A (qdef A)).card=5) :
    (onNodes A).card=5 := by
  obtain ⟨_,_,_,_,_,h3,h4,_,_,he5,_⟩ := order8_ten_stage_chart ha ho
  have hn : 4 ≤ (supportedNodes A (qdef A)).card := by rcases hN with hh|hh <;> omega
  obtain ⟨P,_,_,_,_,hP⟩ := two_curve_head h3 h4 (by omega)
  have hbudget : (supportedNodes A (qdef A)).card+2 ≤ 8 := by rcases hN with hh|hh <;> omega
  have hoff : ∀ x∈supportedNodes A (qdef A), offWeight A b x=0 :=
    fun x hx => offWeight_eq_zero_from_head ho P hP hbudget x hx
  have hM : 5 ≤ (onNodes A).card := five_on_of_aggregate_zero (s:=9) ha ho (by decide) hoff
  by_contra hne
  have hr := gradeFiveState_rank (by omega : 6 ≤ (onNodes A).card) hn
  have hL := Submodule.finrank_mono (gradeFiveStateSpace_le A)
  omega

theorem order9_reduced_off_count_chart
    {A : Fin 12 → Fin 12 → K} {b : Vec K 12}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 9) :
    let n := (supportedNodes A (qdef A)).card
    n=1 ∨ 5 ≤ n := by
  have ha' := order9_off_count_chart ha ho
  dsimp only at ha' ⊢
  have h4 := order9_no_four_off_nodes ha ho
  omega

end RKCert.Paired

