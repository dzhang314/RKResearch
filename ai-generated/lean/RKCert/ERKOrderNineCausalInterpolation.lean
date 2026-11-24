module

public import RKCert.ERKLowSaturation
public import RKCert.ERKLowReverseChart

@[expose] public section

/-! # Causal interpolation obstruction at rank ten

Physical incoming actions are compared through the full grade-four
space, not by identifying rows that share a coordinate or feature. -/
namespace RKCert.Paired
open Module
open scoped Classical

variable {K : Type*} [Field K] {s : ℕ}

/-- The grade-q evaluation rows strictly before the indicated stage
are independent, expressed as a full-coordinate annihilator statement. -/
def IndependentBefore (U : Submodule K (Vec K s)) (j : Fin s) : Prop :=
  ∀ r ∈ annih U, (∀ i, j ≤ i → r i=0) → r=0

theorem transMat_zero_from_prefix {A : Fin s → Fin s → K} {j : Fin s} (ha : StrictLower A)
    {w : Vec K s} (pre : ∀ i, j < i → w i=0) :
    ∀ i, j ≤ i → transMat A w i=0 := by
  intro i hi
  rw [mat_apply]
  apply Finset.sum_eq_zero
  intro l _
  by_cases hl : j < l
  · rw [pre l hl,mul_zero]
  · rw [ha l i ((le_of_not_gt hl).trans hi),zero_mul]

/-- No nonzero annihilator line can be located entirely on one clock
and end at the next stage when the preceding rows are independent. -/
theorem order9_no_causal_clock_contrast
    {A : Fin 12 → Fin 12 → K} {b w : Vec K 12} {j : Fin 12}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 9)
    (rank : finrank K (treeSpace A 5)=10)
    (pre : IndependentBefore (treeSpace A 4) j)
    (wa : w∈annih (treeSpace A 5)) (wn : w≠0)
    (supportEnd : ∀ i, j < i → w i=0)
    (on : ∀ i, w i≠0 → nodes A i=nodes A j) : False := by
  have a0 : transMat A w=0 :=
    pre _ (transMat_mem_annih_pred (j:=4) wa) (transMat_zero_from_prefix ha supportEnd)
  have d : diag (mirror A) w=(1-nodes A j) • w := by
    ext i
    by_cases e : w i=0
    · simp [diag_apply,e]
    · simp [diag_apply,mirror,on i e]
  let U : Submodule K (Vec K 12) := Submodule.span K {w}
  have aw : U≤annih (treeSpace A 5) := (Submodule.span_singleton_le_iff_mem ..).mpr wa
  have ⟨_,_,_,_,_,kill⟩ := order9_rank_five_full ha ho rank
  have eq := kill U aw
    (fun v hv => by
      obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hv
      rw [map_smul,a0,smul_zero]
      exact U.zero_mem)
    (fun v hv => by
      obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hv
      rw [map_smul,d]
      exact U.smul_mem _ (U.smul_mem _ (Submodule.mem_span_singleton_self _)))
  have wm : w∈U := Submodule.mem_span_singleton_self _
  rw [eq,Submodule.mem_bot] at wm
  exact wn wm

/-- Actual causal interpolation lemma: at rank ten the next stage
cannot be interpolated by prior grade-five evaluations at its own clock.
The interpolation weights may be arbitrary signed coefficients. -/
theorem order9_forbid_same_clock_interpolation
    {A : Fin 12 → Fin 12 → K} {b w : Vec K 12} {j : Fin 12}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 9)
    (rank : finrank K (treeSpace A 5)=10)
    (pre : IndependentBefore (treeSpace A 4) j)
    (prev : ∀ i, j ≤ i → w i=0)
    (clock : ∀ i, w i≠0 → nodes A i=nodes A j)
    (fit : ∀ v∈treeSpace A 5, v j=row w v) : False := by
  let q := Pi.single j 1-w
  have qj : q j=1 := by simp [q,prev j le_rfl]
  have qn : q≠0 := by intro e; rw [e] at qj; exact zero_ne_one qj
  have qr : q∈annih (treeSpace A 5) := by
    apply mem_annih.mpr
    intro v hv
    have e : row (Pi.single j 1) v=v j := by simp [row_apply,Pi.single_apply]
    change rowL (Pi.single j 1-w) v=0
    rw [map_sub,LinearMap.sub_apply,rowL_apply,rowL_apply,e,fit _ hv,sub_self]
  apply order9_no_causal_clock_contrast ha ho rank pre qr qn
  · intro i hi
    simp [q,ne_of_gt hi,prev i hi.le]
  · intro i hi
    by_cases e : i=j
    · simp [e]
    · apply clock i
      intro z
      apply hi
      simp [q,e,z]

end RKCert.Paired
