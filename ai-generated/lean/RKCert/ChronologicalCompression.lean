module

public import RKCert.GradeSeparation
public import Mathlib.Data.Finset.Sort

@[expose] public section

/-! # Chronological compression of actual stage spaces -/
namespace RKCert.Paired

variable {K : Type*} [Field K] {s n : ℕ}

/-- Evaluation on a fixed subspace. -/
def coordOn (H : Submodule K (Vec K s)) (i : Fin s) : H →ₗ[K] K :=
  (LinearMap.proj i).comp H.subtype

@[simp] theorem coordOn_apply (H : Submodule K (Vec K s)) (i : Fin s) (v : H) :
    coordOn H i v = (v : Vec K s) i := rfl

/-- A causal pivot is a stage evaluation not spanned by earlier evaluations. -/
def IsCoordPivot (H : Submodule K (Vec K s)) (i : Fin s) : Prop :=
  coordOn H i ∉ Submodule.span K {f | ∃ j : Fin s, j < i ∧ f = coordOn H j}

/-- All evaluations are recovered from pivots at or before their own index. -/
theorem coordOn_mem_pivot_span (H : Submodule K (Vec K s)) (i : Fin s) :
    coordOn H i ∈ Submodule.span K {f | ∃ j : Fin s, IsCoordPivot H j ∧ j ≤ i ∧ f = coordOn H j} := by
  apply (wellFounded_lt (α:=Fin s)).induction i
  intro i ih
  by_cases hi : IsCoordPivot H i
  · exact Submodule.subset_span ⟨i,hi,le_rfl,rfl⟩
  · change ¬ (coordOn H i ∉ Submodule.span K {f | ∃ j : Fin s, j < i ∧ f = coordOn H j}) at hi
    have hsub : Submodule.span K {f | ∃ j : Fin s, j < i ∧ f = coordOn H j} ≤
        Submodule.span K {f | ∃ k : Fin s, IsCoordPivot H k ∧ k ≤ i ∧ f = coordOn H k} := by
      apply Submodule.span_le.mpr
      rintro _ ⟨j,hj,rfl⟩
      apply Submodule.span_mono _ (ih j hj)
      rintro f ⟨k,hk,hkj,hf⟩
      exact ⟨k,hk,hkj.trans hj.le,hf⟩
    exact hsub (not_not.mp hi)

/-- Restriction of a column to selected coordinates. -/
def restrictCol (e : Fin n → Fin s) : Vec K s →ₗ[K] Vec K n where
  toFun x := x ∘ e
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem restrictCol_apply (e : Fin n → Fin s) (x : Vec K s) (i : Fin n) :
    restrictCol e x i = x (e i) := rfl

theorem exists_causal_coord_family (H : Submodule K (Vec K s)) :
    ∃ (n : ℕ) (e : Fin n ↪o Fin s) (w : Fin s → Fin n → K),
      (∀ i j, i < e j → w i j = 0) ∧
      (∀ (v : Vec K s), v ∈ H → ∀ i, ∑ j, w i j * v (e j) = v i) ∧
      (∀ i, IsCoordPivot H (e i)) := by
  classical
  let T := Finset.univ.filter (IsCoordPivot H)
  let e := T.orderEmbOfFin rfl
  have hex (i : Fin s) : ∃ a : Fin T.card → K, (∀ j, i < e j → a j=0) ∧
      (∑ j, a j • coordOn H (e j)) = coordOn H i := by
    let v (j : Fin T.card) : H →ₗ[K] K := if e j ≤ i then coordOn H (e j) else 0
    have hsub : Submodule.span K {f | ∃ j, IsCoordPivot H j ∧ j ≤ i ∧ f=coordOn H j} ≤
        Submodule.span K (Set.range v) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨j,hj,hji,rfl⟩
      have hr : j ∈ Set.range e := by
        rw [Finset.range_orderEmbOfFin]
        simpa [T] using hj
      obtain ⟨k,rfl⟩ := hr
      exact Submodule.subset_span ⟨k,by simp [v,hji]⟩
    obtain ⟨a,ha⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp
      (hsub (coordOn_mem_pivot_span H i))
    refine ⟨fun j => if e j ≤ i then a j else 0, ?_, ?_⟩
    · intro j hj; simp [not_le_of_gt hj]
    · rw [← ha]
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : e j ≤ i <;> simp [v,h]
  choose w hw0 hw using hex
  refine ⟨T.card,e,w,hw0,?_,?_⟩
  · intro v hv i
    have h := LinearMap.congr_fun (hw i) ⟨v,hv⟩
    simpa only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, coordOn_apply] using h
  · intro j
    have h := T.orderEmbOfFin_mem rfl j
    change (e j) ∈ Finset.univ.filter (IsCoordPivot H) at h
    exact (Finset.mem_filter.mp h).2

theorem restrictCol_inj_on {H : Submodule K (Vec K s)} {e : Fin n → Fin s}
    {w : Fin s → Fin n → K}
    (hw : ∀ (v : Vec K s), v ∈ H → ∀ i, ∑ j, w i j * v (e j) = v i) :
    Set.InjOn (restrictCol e) (H : Set (Vec K s)) := by
  intro u hu v hv huv
  ext i
  rw [← hw u hu i, ← hw v hv i]
  apply Finset.sum_congr rfl
  intro j _
  rw [show u (e j) = v (e j) from congrFun huv j]

/-- Exact compression, by substituting earlier-coordinate reconstructions in
each retained row. This matrix is strictly triangular in the retained order. -/
def compressMat (A : Fin s → Fin s → K) (e : Fin n → Fin s)
    (w : Fin s → Fin n → K) (i j : Fin n) : K :=
  ∑ k, A (e i) k * w k j

theorem compress_strict {A : Fin s → Fin s → K} (ha : StrictLower A)
    (e : Fin n ↪o Fin s) (w : Fin s → Fin n → K)
    (hw : ∀ i j, i < e j → w i j = 0) : StrictLower (compressMat A e w) := by
  intro i j hij
  unfold compressMat
  apply Finset.sum_eq_zero
  intro k _
  by_cases h : e i ≤ k
  · rw [ha _ _ h,zero_mul]
  · rw [hw _ _ ((lt_of_not_ge h).trans_le (e.monotone hij)),mul_zero]

theorem compress_mat_comm {H : Submodule K (Vec K s)} (A : Fin s → Fin s → K)
    (e : Fin n → Fin s) (w : Fin s → Fin n → K)
    (hw : ∀ (v : Vec K s), v ∈ H → ∀ i, ∑ j, w i j * v (e j) = v i)
    (v : Vec K s) (hv : v∈H) :
    mat (compressMat A e w) (restrictCol e v) = restrictCol e (mat A v) := by
  ext i
  simp only [restrictCol_apply, mat_apply, compressMat, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [← hw v hv k,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- A chronological compression retains each actual tree column through one
grade beyond the space used to construct it. -/
theorem restrict_stageWeight (A : Fin s → Fin s → K) (B : Fin n → Fin n → K)
    (e : Fin n → Fin s) (q : ℕ)
    (hc : ∀ v ∈ treeSpace A q, mat B (restrictCol e v) = restrictCol e (mat A v))
    (t : Tree) (ht : t.order≤q+2) :
    restrictCol e (stageWeight A t) = stageWeight B t := by
  induction t with
  | leaf => rfl
  | attach t u iht ihu =>
    change t.order+u.order≤q+2 at ht
    have h1 := t.order_pos
    have h2 := u.order_pos
    have hA := hc (stageWeight A t) (stageWeight_mem_space A t (by omega))
    rw [iht (by omega)] at hA
    ext i
    have hm := congrFun hA i
    have hr := congrFun (ihu (by omega)) i
    simpa only [restrictCol_apply,stageWeight,mat_apply] using
      congrArg₂ (· * ·) hm.symm hr

theorem restrict_normTree (A : Fin s → Fin s → K) (B : Fin n → Fin n → K)
    (e : Fin n → Fin s) (q : ℕ)
    (hc : ∀ v ∈ treeSpace A q, mat B (restrictCol e v) = restrictCol e (mat A v))
    (t : Tree) (ht : t.order≤q+2) : restrictCol e (normTree A t)=normTree B t := by
  rw [normTree,normTree,map_smul,restrict_stageWeight A B e q hc t ht]

theorem restrict_zeroSpace (A : Fin s → Fin s → K) (B : Fin n → Fin n → K)
    (e : Fin n → Fin s) {q k : ℕ} (hk : k≤q+1)
    (hc : ∀ v ∈ treeSpace A q, mat B (restrictCol e v) = restrictCol e (mat A v)) :
    (zeroSpace A k).map (restrictCol e) = zeroSpace B k := by
  simp only [zeroSpace,Submodule.map_span]
  congr 1
  ext v
  constructor
  · rintro ⟨_,⟨t,u,he,ht,rfl⟩,rfl⟩
    exact ⟨t,u,he,ht,by rw [map_sub,restrict_normTree A B e q hc t (by omega),
      restrict_normTree A B e q hc u (by omega)]⟩
  · rintro ⟨t,u,he,ht,rfl⟩
    exact ⟨_,⟨t,u,he,ht,rfl⟩,by rw [map_sub,restrict_normTree A B e q hc t (by omega),
      restrict_normTree A B e q hc u (by omega)]⟩

theorem restrict_polyEval (A : Fin s → Fin s → K) (B : Fin n → Fin n → K)
    (e : Fin n → Fin s) (q : ℕ)
    (hc : ∀ v ∈ treeSpace A q, mat B (restrictCol e v) = restrictCol e (mat A v))
    (a : Fin (q+1) → K) :
    restrictCol e (polyEval A q a) = polyEval B q a := by
  rw [polyEval_apply,polyEval_apply,map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul,restrict_normTree A B e q hc]
  rw [Tree.order_bush]; omega

/-- If two retained rows gave the same tree evaluations, the later one would
not have been selected as a chronological pivot. -/
theorem compressed_rows_distinct (A : Fin s → Fin s → K) (B : Fin n → Fin n → K)
    (e : Fin n ↪o Fin s) (q : ℕ)
    (hc : ∀ v ∈ treeSpace A q, mat B (restrictCol e v) = restrictCol e (mat A v))
    (hp : ∀ i, IsCoordPivot (treeSpace A q) (e i))
    {i j : Fin n} (hij : i < j) :
    ∃ t : Tree, t.order ≤ q+1 ∧ stageWeight B t i ≠ stageWeight B t j := by
  by_contra! he
  have hEq : coordOn (treeSpace A q) (e i) = coordOn (treeSpace A q) (e j) := by
    ext v
    obtain ⟨v,hv⟩ := v
    simp only [coordOn_apply]
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨t,ht,rfl⟩ := hx
      have h := restrict_stageWeight A B e q hc t (by omega)
      calc
        stageWeight A t (e i) = stageWeight B t i := congrFun h i
        _ = stageWeight B t j := he t ht
        _ = stageWeight A t (e j) := (congrFun h j).symm
    | zero => rfl
    | add x y _ _ hh hk => simp [hh,hk]
    | smul r x _ hh => simp [hh]
  apply hp j
  exact Submodule.subset_span ⟨e i,e.strictMono hij,hEq.symm⟩

end RKCert.Paired
