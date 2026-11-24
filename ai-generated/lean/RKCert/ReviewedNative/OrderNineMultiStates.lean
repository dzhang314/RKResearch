module

public import RKCert.ReviewedNative.OrderNineMultiMoments
public import RKCert.ReviewedNative.OrderNineGradeFive

@[expose] public section

/-! # Distinct-state interpolation in the actual two-curve chart

State equality is used only for evaluations. It does not identify or merge
physical rows. The coefficients are recovered by exact interpolation.
-/
namespace RKResearch.Certified.Graded.MultiOff
open RKResearch Module Polynomial OneOff
open scoped Matrix Classical

variable {K : Type*} [Field K] {s : ℕ}

theorem coordinate_as_single (i : Fin s) : Reverse.coordinate (K:=K) i = Pi.single i 1 := by
  ext j
  by_cases eq : j=i
  · subst j; simp [Reverse.coordinate]
  · simp [Reverse.coordinate,eq]

noncomputable def onOffEval (A : Matrix (Fin s) (Fin s) K) :
    (((cleanKnots A) → K) × ((offKnots A) → K)) →ₗ[K] (Fin s → K) where
  toFun z i := if h : g A i=0 then z.1 ⟨nodes A i,mem_cleanKnots.mpr ⟨i,h,rfl⟩⟩
    else z.2 ⟨nodes A i,mem_offKnots.mpr ⟨i,h,rfl⟩⟩
  map_add' x y := by ext i; dsimp; split <;> rfl
  map_smul' a x := by ext i; dsimp; split <;> rfl

noncomputable def onOffSpace (A : Matrix (Fin s) (Fin s) K) : Submodule K ((Fin s → K)) :=
  LinearMap.range (onOffEval A)

theorem onOffEval_on (A : Matrix (Fin s) (Fin s) K) (z) {i : Fin s} (hi : g A i=0) :
    onOffEval A z i = z.1 ⟨nodes A i,mem_cleanKnots.mpr ⟨i,hi,rfl⟩⟩ := dite_eq_left hi

theorem onOffEval_off (A : Matrix (Fin s) (Fin s) K) (z) {i : Fin s} (hi : g A i≠0) :
    onOffEval A z i = z.2 ⟨nodes A i,mem_offKnots.mpr ⟨i,hi,rfl⟩⟩ := dite_eq_right hi

theorem onOffEval_injective (A : Matrix (Fin s) (Fin s) K) : Function.Injective (onOffEval A) := by
  intro x y h
  apply Prod.ext
  · funext a
    obtain ⟨i,hi,hc⟩ := mem_cleanKnots.mp a.property
    have he := congrFun h i
    rw [onOffEval_on A x hi,onOffEval_on A y hi] at he
    have ha : (⟨nodes A i,mem_cleanKnots.mpr ⟨i,hi,rfl⟩⟩ : cleanKnots A)=a := Subtype.ext hc
    rwa [ha] at he
  · funext a
    obtain ⟨i,hi,hc⟩ := mem_offKnots.mp a.property
    have he := congrFun h i
    rw [onOffEval_off A x hi,onOffEval_off A y hi] at he
    have ha : (⟨nodes A i,mem_offKnots.mpr ⟨i,hi,rfl⟩⟩ : offKnots A)=a :=
      Subtype.ext hc
    rwa [ha] at he

theorem onOffSpace_rank (A : Matrix (Fin s) (Fin s) K) :
    finrank K (onOffSpace A) = (cleanKnots A).card + (offKnots A).card := by
  rw [onOffSpace,LinearMap.finrank_range_of_inj (onOffEval_injective A),Module.finrank_prod,
    Module.finrank_fintype_fun_eq_card,Module.finrank_fintype_fun_eq_card,
    Fintype.card_coe,Fintype.card_coe]

theorem onOffSpace_diag {A : Matrix (Fin s) (Fin s) K} {v : (Fin s → K)} (hv : v∈onOffSpace A) :
    diag (nodes A) v ∈ onOffSpace A := by
  obtain ⟨z,rfl⟩ := hv
  refine ⟨(fun a => a.val*z.1 a,fun a => a.val*z.2 a),?_⟩
  ext i
  by_cases h : g A i=0
  · rw [onOffEval_on A _ h,diag_apply,onOffEval_on A _ h]
  · rw [onOffEval_off A _ h,diag_apply,onOffEval_off A _ h]

theorem pairProfile_mem_onOffSpace {A : Matrix (Fin s) (Fin s) K} {P : K[X]}
    (hP : ∀ i, g A i≠0 → P.eval (nodes A i)=g A i) (Q R : K[X]) :
    evalNodes A Q+diag (g A) (evalNodes A R)∈onOffSpace A := by
  refine ⟨(fun a => Q.eval a.val,fun a => Q.eval a.val + P.eval a.val*R.eval a.val),?_⟩
  ext i
  by_cases h : g A i=0
  · rw [onOffEval_on A _ h]
    simp [h]
  · rw [onOffEval_off A _ h]
    simp [hP i h]

noncomputable def gradeFiveStateMap (A : Matrix (Fin s) (Fin s) K) : ((Fin 6 → K) × (Fin 4 → K)) →ₗ[K] (Fin s → K) :=
  (coeffEval A 5).coprod ((diag (g A)).comp (coeffEval A 3))

noncomputable def gradeFiveStateSpace (A : Matrix (Fin s) (Fin s) K) : Submodule K ((Fin s → K)) :=
  LinearMap.range (gradeFiveStateMap A)

theorem pairProfile_mem_E5 (A : Matrix (Fin s) (Fin s) K) (Q R : K[X])
    (hQ : Q.natDegree ≤ 5) (hR : R.natDegree ≤ 3) :
    evalNodes A Q + diag (g A) (evalNodes A R) ∈ treeSpace A 5 := by
  apply (treeSpace A 5).add_mem (evalNodes_mem_treeSpace A Q hQ)
  apply zeroSpace_le_treeSpace A 5
  apply band_le A 3
  exact band_iff.mpr ⟨R,hR,rfl⟩

theorem gradeFiveStateMap_eq_eval (A : Matrix (Fin s) (Fin s) K) (z : (Fin 6 → K) × (Fin 4 → K)) :
    gradeFiveStateMap A z = evalNodes A (ofFn 6 z.1) + diag (g A) (evalNodes A (ofFn 4 z.2)) := by
  rw [ofFn_eval A 5,ofFn_eval A 3]
  rfl

theorem gradeFiveStateSpace_le (A : Matrix (Fin s) (Fin s) K) :
    gradeFiveStateSpace A ≤ treeSpace A 5 := by
  rintro _ ⟨z,rfl⟩
  rw [gradeFiveStateMap_eq_eval]
  apply pairProfile_mem_E5
  · exact Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) _)
  · exact Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) _)

theorem gradeFiveState_injective {A : Matrix (Fin s) (Fin s) K} (hM : 6 ≤ (cleanKnots A).card)
    (hN : 4 ≤ (offKnots A).card) : Function.Injective (gradeFiveStateMap A) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  let Q := ofFn 6 z.1
  let R := ofFn 4 z.2
  have hQ : Q.natDegree ≤ 5 := Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) _)
  have hR : R.natDegree ≤ 3 := Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) _)
  have he (i : Fin s) : Q.eval (nodes A i)+g A i*R.eval (nodes A i)=0 := by
    rw [gradeFiveStateMap_eq_eval] at hz
    exact congrFun hz i
  have hQ0 : Q=0 := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' Q (cleanKnots A)
    (fun x hx => by
      obtain ⟨i,hi,rfl⟩ := mem_cleanKnots.mp hx
      simpa [hi] using he i) (by omega)
  have hR0 : R=0 := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' R (offKnots A)
    (fun x hx => by
      obtain ⟨i,hi,rfl⟩ := mem_offKnots.mp hx
      exact (mul_eq_zero.mp (by simpa [hQ0] using he i)).resolve_left hi) (by omega)
  exact Prod.ext (injective_ofFn 6 (hQ0.trans (ofFn_zero _).symm))
    (injective_ofFn 4 (hR0.trans (ofFn_zero _).symm))

theorem gradeFiveState_rank {A : Matrix (Fin s) (Fin s) K} (hM : 6 ≤ (cleanKnots A).card)
    (hN : 4 ≤ (offKnots A).card) : finrank K (gradeFiveStateSpace A)=10 := by
  rw [gradeFiveStateSpace,LinearMap.finrank_range_of_inj (gradeFiveState_injective hM hN),
    Module.finrank_prod,Module.finrank_fin_fun,Module.finrank_fin_fun]

/-- Evaluation separately on the two branches permits all state vectors
of size ≤ six on and ≤ four off to be interpolated inside E5. -/
theorem onOffSpace_le_E5 {A : Matrix (Fin s) (Fin s) K} {P : K[X]}
    (hP : ∀ i, g A i≠0 → P.eval (nodes A i)=g A i)
    (hM : (cleanKnots A).card ≤ 6) (hN : (offKnots A).card ≤ 4) :
    onOffSpace A ≤ treeSpace A 5 := by
  rintro _ ⟨z,rfl⟩
  let T := cleanKnots A
  let S := offKnots A
  let f (x : K) : K := if h : x∈T then z.1 ⟨x,h⟩ else 0
  let Q := Lagrange.interpolate T id f
  have hQ : Q.natDegree ≤ 5 := by
    change T.card ≤ 6 at hM
    by_cases h : Q=0
    · simp [h]
    · have hh := (Polynomial.natDegree_lt_iff_degree_lt h).mpr
          (Lagrange.degree_interpolate_lt f (Set.injOn_id _))
      omega
  have heQ (a : K) (ha : a∈T) : Q.eval a=f a :=
    Lagrange.eval_interpolate_at_node f (Set.injOn_id _) ha
  let adjust (x : K) : K := if h : x∈S then (z.2 ⟨x,h⟩-Q.eval x)/P.eval x else 0
  let R := Lagrange.interpolate S id adjust
  have hR : R.natDegree ≤ 3 := by
    change S.card ≤ 4 at hN
    by_cases h : R=0
    · simp [h]
    · have hh := (Polynomial.natDegree_lt_iff_degree_lt h).mpr
          (Lagrange.degree_interpolate_lt adjust (Set.injOn_id _))
      omega
  have heR (a : K) (ha : a∈S) : R.eval a=adjust a :=
    Lagrange.eval_interpolate_at_node adjust (Set.injOn_id _) ha
  have hv : onOffEval A z = evalNodes A Q + diag (g A) (evalNodes A R) := by
    ext i
    by_cases h : g A i=0
    · have hm : nodes A i∈T := mem_cleanKnots.mpr ⟨i,h,rfl⟩
      rw [onOffEval_on A _ h]
      simp [h,heQ _ hm,f,dite_eq_left hm]
    · have hm : nodes A i∈S := mem_offKnots.mpr ⟨i,h,rfl⟩
      rw [onOffEval_off A _ h]
      simp only [Pi.add_apply,evalNodes_apply,diag_apply,heR _ hm,adjust,dite_eq_left hm,hP i h]
      rw [mul_div_cancel₀ _ h]
      ring
  rw [hv]
  exact pairProfile_mem_E5 A Q R hQ hR

theorem state_single_is_unique_off {A : Matrix (Fin s) (Fin s) K} {i j : Fin s}
    (hi : Pi.single i 1 ∈ onOffSpace A) (hdi : g A i≠0) (hdj : g A j≠0)
    (hc : nodes A j=nodes A i) : j=i := by
  obtain ⟨z,hz⟩ := hi
  have he : onOffEval A z j=onOffEval A z i := by
    rw [onOffEval_off A _ hdj,onOffEval_off A _ hdi]
    have h : (⟨nodes A j,mem_offKnots.mpr ⟨j,hdj,rfl⟩⟩ : offKnots A) =
        ⟨nodes A i,mem_offKnots.mpr ⟨i,hdi,rfl⟩⟩ := Subtype.ext hc
    rw [h]
  rw [hz] at he
  by_contra h
  simp [h] at he

/-- A unique off state with a nonzero weight cannot lie in a state-valued
terminal coordinate once the off weights cancel in each state. -/
theorem on_of_state_single {A : Matrix (Fin s) (Fin s) K} {b : (Fin s → K)} {i : Fin s}
    (hA : Pi.single i 1 ∈ onOffSpace A) (hbi : b i≠0)
    (hoff : ∀ x∈offKnots A, offMass A b x=0) :
    g A i=0 := by
  by_contra hd
  have he := hoff _ (mem_offKnots.mpr ⟨i,hd,rfl⟩)
  unfold offMass at he
  rw [Finset.sum_eq_single i] at he
  · simp [hd,hbi] at he
  · intro j _ hj
    have h : ¬ (g A j≠0 ∧ nodes A j=nodes A i) :=
      fun hh => hj (state_single_is_unique_off hA hd hh.1 hh.2)
    simp [h]
  · simp

variable [CharZero K]

/-- If at least four off states have cancelling aggregate weights, a
hypothetical order-nine twelve-stage tableau has at most six on states. -/
theorem order9_on_count_le_six {A : Matrix (Fin 12) (Fin 12) K} {b : (Fin 12 → K)}
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 9 A b)
    (hN : 4 ≤ (offKnots A).card) (P : K[X])
    (hP : ∀ i, g A i≠0 → P.eval (nodes A i)=g A i)
    (hoff : ∀ x∈offKnots A, offMass A b x=0) :
    (cleanKnots A).card ≤ 6 := by
  by_contra! hM
  have he5 := order9_grade_five_upper ha ho
  have hr := gradeFiveState_rank (by omega : 6 ≤ (cleanKnots A).card) hN
  have hE := Submodule.eq_of_le_of_finrank_le (gradeFiveStateSpace_le A) (by omega)
  have h10 : finrank K (treeSpace A 5)=10 := by rw [←hE,hr]
  obtain ⟨hb,_,he,_⟩ := order9_rank_five_full_terminal ha ho h10
  let i := Fin.last 11
  have hs : Pi.single i 1∈gradeFiveStateSpace A := by
    rw [hE]
    simpa only [coordinate_as_single,i] using he
  obtain ⟨z,hz⟩ := hs
  rw [gradeFiveStateMap_eq_eval] at hz
  let Q : K[X] := ofFn 6 z.1
  let R : K[X] := ofFn 4 z.2
  change evalNodes A Q + diag (g A) (evalNodes A R) = Pi.single i 1 at hz
  have hi := on_of_state_single (hz ▸ pairProfile_mem_onOffSpace hP Q R) hb hoff
  have hQ : Q.natDegree ≤ 5 := Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) _)
  have heq (j : Fin 12) (hj : g A j=0) : Q.eval (nodes A j) = (Pi.single i (1:K) : (Fin 12 → K)) j := by
    have h := congrFun hz j
    simpa [hj] using h
  let T := (cleanKnots A).erase (nodes A i)
  have hTc : T.card + 1=(cleanKnots A).card := Finset.card_erase_add_one
    (mem_cleanKnots.mpr ⟨i,hi,rfl⟩)
  have hzQ : Q=0 := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' Q T (fun x hx => by
    obtain ⟨hxc,hxo⟩ := Finset.mem_erase.mp hx
    obtain ⟨j,hj,hxj⟩ := mem_cleanKnots.mp hxo
    have hji : j≠i := fun h => hxc (hxj.symm.trans (congrArg (nodes A) h))
    rw [←hxj,heq j hj]
    simp [hji]) (by omega)
  simpa [hzQ] using heq i hi

end RKResearch.Certified.Graded.MultiOff

