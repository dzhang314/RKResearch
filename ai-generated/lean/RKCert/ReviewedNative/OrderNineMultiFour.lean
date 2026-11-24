module

public import RKCert.ReviewedNative.OrderNineMultiStates
public import RKCert.ReviewedNative.OneOffTailClockRank

@[expose] public section

/-! # The four-off branch at order nine

The excluded endpoint on a five-node on rule follows from a rational
four-row moment identity. No sign assumption or analysis is needed.
-/
namespace RKResearch.Certified.Graded.MultiOff
open RKResearch Module Polynomial OneOff Reverse RKCert.Endpoint
open scoped Matrix Classical

variable {K : Type*} [Field K] [CharZero K] {s : ℕ}

omit [CharZero K] in
theorem zero_mem_cleanKnots {A : Matrix (Fin (s+1)) (Fin (s+1)) K}
    (ha : ∀ i j, i≤j → A i j=0) : 0∈cleanKnots A := by
  apply mem_cleanKnots.mpr
  refine ⟨0,origin_zeroSpace ha 2 (mDef_mem A 1),?_⟩
  change (∑ j, A 0 j * 1) = 0
  exact Finset.sum_eq_zero fun j _ => by rw [ha 0 j (Fin.zero_le _),zero_mul]

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
theorem one_not_on_of_five {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : (Fin (s+1)→K)}
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder A b 9)
    (hM : (cleanKnots A).card=5)
    (hoff : ∀ x∈offKnots A, offMass A b x=0) :
    (1:K)∉cleanKnots A := by
  intro h1
  let T := (cleanKnots A).erase 1
  have h0 : (0:K)∈T := Finset.mem_erase.mpr ⟨zero_ne_one,zero_mem_cleanKnots ha⟩
  let S := T.erase 0
  have hT : T.card+1=(cleanKnots A).card := Finset.card_erase_add_one h1
  have hS : S.card+1=T.card := Finset.card_erase_add_one h0
  let Q : K[X] := ∏ a∈S, (X-C a)
  have hm : Q.Monic := Polynomial.monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _
  have hd : Q.natDegree=3 := by
    have he : Q.natDegree=S.card := by simp [Q]
    omega
  let P := (X^2-X)*Q
  have hroots (a : K) (ha : a∈cleanKnots A) : P.eval a=0 := by
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
    simp only [probe,row_apply,dotProduct,evalNodes_apply,←Finset.sum_sub_distrib,P,eval_mul,eval_sub,eval_pow,eval_X]
    apply Finset.sum_congr rfl
    intro i _
    simp only [pow_add,pow_one]
    ring
  have hh (i : Fin 4) :
      (∑ j : Fin 4, Q.coeff j.val / ((i.val+j.val+3:ℕ):K)) -
        (∑ j : Fin 4, Q.coeff j.val / ((i.val+j.val+2:ℕ):K))=0 := by
    have h := probe_zero_of_clean_roots hoff P hroots i.val
    rw [he,evalNodes_eq_coeffEval A Q hd.le,probe_coeffEval ho (by have := i.isLt; omega),
      probe_coeffEval ho (by have := i.isLt; omega)] at h
    have e (j : Fin 4) : i.val+2+j.val+1=i.val+j.val+3 := by omega
    have e' (j : Fin 4) : i.val+1+j.val+1=i.val+j.val+2 := by omega
    simpa only [e,e'] using h
  have hz := cubic_beta_moments_top_zero _ hh
  have hc : Q.coeff 3=1 := by
    rw [←hd, ←Polynomial.leadingCoeff, hm.leadingCoeff]
  exact (one_ne_zero : (1:K)≠0) (hc.symm.trans hz)

omit [CharZero K] in
theorem onOffSpace_adjoin_single_clock {A : Matrix (Fin s) (Fin s) K} (i : Fin s) :
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


/-- With or without a full fifth rank, the fifth tree space cannot be
clock-stable. The two missing reflected clock blocks cost two dimensions
of the adjacent annihilator. At full rank the checked terminal refinement
already pays its extra independent coordinate. -/
theorem grade_five_not_stable {A : Matrix (Fin 12) (Fin 12) K} {b : Fin 12→K}
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder A b 9) :
    ¬ (treeSpace A 5).map (diag (nodes A)) ≤ treeSpace A 5 := by
  by_cases full : finrank K (treeSpace A 5)=10
  · exact order9_grade_five_clock_noninvariant ha ho full
  intro inv
  let U := annih (treeSpace A 5)
  let Z := annih (treeSpace A 4)
  let c := reflectedClock A
  have clock (v : Fin 12 → K) (hv : v∈U) : diag c v∈U := by
    have e : diag c v=v-diag (nodes A) v := by
      ext i; simp only [c,reflectedClock,diag_apply,Pi.sub_apply,Pi.one_apply,sub_mul,one_mul]
    rw [e]
    exact U.sub_mem hv (annih_map_diag (Submodule.map_le_iff_le_comap.mp inv)
      (Submodule.mem_map_of_mem hv))
  have mass (v : Fin 12→K) (hv : v∈U) : ∑i,v i=0 := by
    simpa only [row_apply,dotProduct,Pi.one_apply,mul_one] using
      mem_annih.mp hv _ (one_mem_treeSpace A 5)
  have moments (k : ℕ) (pay : k+1≤9) : ∑i,(c i)^k*b i=((k+1:ℕ):K)⁻¹ := by
    have e : (∑i,(c i)^k*b i)=reflectedProbe A b 0 k 1 := by
      simp only [row_apply,dotProduct,Pi.one_apply,pow_zero,mul_one,c]
      exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    rw [e,←one_div]
    apply (eq_div_iff (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k))).mpr
    simpa only [mul_comm] using reflected_power_mass ho k pay
  have mask := clock_mask_invariant clock
  have fail := two_failed_of_three_moments c b U mask mass
    (by simpa [one_div] using moments 1 (by decide))
    (by simpa [one_div] using moments 2 (by decide))
    (by simpa [one_div] using moments 3 (by decide))
  have shrink := ordered_hermite_outgoing Fin.revPerm _ (causal_transpose ha) c b U Z mask
    (annih_antitone (treeSpace_mono A (by decide : 4≤5)))
    (fun _ hv => annih_map_transpose (mat_treeSpace A 4) (Submodule.mem_map_of_mem hv)) 2 fail
    (fun P hp => reverse_primitive_paid ho 4 P 3 (by omega) (by decide))
  have e4 := (order9_forward_chart ha ho (by decide)).2.2.2.2
  have e5 := order9_grade_five_upper ha ho
  have ur := finrank_annih (treeSpace A 5)
  have zr := finrank_annih (treeSpace A 4)
  change finrank K (treeSpace A 5)+finrank K U=12 at ur
  change finrank K (treeSpace A 4)+finrank K Z=12 at zr
  omega

/-- The actual four-off branch of the twelve-stage order-nine chart is
impossible, including all repeated-state configurations. -/
theorem order9_no_four_off_nodes {A : Matrix (Fin 12) (Fin 12) K} {b : (Fin 12→K)}
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder A b 9) :
    (offKnots A).card≠4 := by
  intro hN
  obtain ⟨_,h3,h4,_⟩ := order9_forward_chart ha ho (by decide)
  have he5hi := order9_grade_five_upper ha ho
  obtain ⟨P,_,_,_,_,hP⟩ := two_curve_head h3 h4 (by omega)
  have hoff : ∀ x∈offKnots A, offMass A b x=0 :=
    fun x hx => offMass_zero_of_head ho hP (by omega) x hx
  have hMlo : 5 ≤ (cleanKnots A).card := many_clean_of_cancel ho (q:=4) (by decide) hoff
  have hMhi := order9_on_count_le_six ha ho (by omega) P hP hoff
  have hLE := onOffSpace_le_E5 hP hMhi hN.le
  have hR := onOffSpace_rank A
  apply grade_five_not_stable ha ho
  by_cases hE : finrank K (treeSpace A 5) ≤ finrank K (onOffSpace A)
  · rw [←Submodule.eq_of_le_of_finrank_le hLE hE]
    apply Submodule.map_le_iff_le_comap.mpr
    intro v hv
    exact onOffSpace_diag hv
  · have hM : (cleanKnots A).card=5 := by omega
    have hE5 : finrank K (treeSpace A 5)=10 := by omega
    obtain ⟨hb,hc,hi,_⟩ := order9_rank_five_full_terminal ha ho hE5
    let i := Fin.last 11
    have hout : Pi.single i 1 ∉ onOffSpace A := by
      intro hw
      have hd := on_of_state_single hw hb hoff
      exact one_not_on_of_five (s:=11) ha ho hM hoff (mem_cleanKnots.mpr ⟨i,hd,hc⟩)
    have inside : Pi.single i 1∈treeSpace A 5 := by simpa only [coordinate_as_single,i] using hi
    have hs : treeSpace A 5=onOffSpace A ⊔ Submodule.span K {Pi.single i 1} := by
      symm
      apply Submodule.eq_of_le_of_finrank_le (sup_le hLE ((Submodule.span_singleton_le_iff_mem ..).mpr inside))
      rw [Submodule.finrank_sup_span_singleton hout,hE5,hR,hN,hM]
    rw [hs]
    exact onOffSpace_adjoin_single_clock i

end RKResearch.Certified.Graded.MultiOff
