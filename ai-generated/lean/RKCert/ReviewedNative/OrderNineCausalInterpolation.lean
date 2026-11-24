module
public import RKCert.ReviewedNative.OrderNineReverseChart

@[expose] public section

/-! # No same-clock interpolation on a paid order-nine prefix -/
namespace RKResearch.Certified.Graded.OneOff
open RKResearch Module Reverse
open scoped Classical Matrix

variable {K : Type*} [Field K] {s : ℕ}

/-- Evaluation by the physical stages strictly before `j) is independent
on `U`, in the full-coordinate annihilator formulation. -/
def IndependentBefore (U : Submodule K (Fin s → K)) (j : Fin s) : Prop :=
  ∀ r ∈ annih U, (∀ i, j ≤ i → r i=0) → r=0

/-- A nonzero single-clock contrast ending at the next stage would be a
jointly invariant line in the paid grade-five annihilator. -/
theorem order9_no_causal_clock_contrast
    {A : Matrix (Fin 12) (Fin 12) K} {b w : Fin 12 → K} {j : Fin 12}
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder A b 9)
    (rank : finrank K (treeSpace A 5)=10)
    (pre : IndependentBefore (treeSpace A 4) j)
    (wa : w∈annih (treeSpace A 5)) (wn : w≠0)
    (supportEnd : ∀ i, j < i → w i=0)
    (on : ∀ i, w i≠0 → nodes A i=nodes A j) : False := by
  have wt : mat A.transpose w ∈ annih (treeSpace A 4) :=
    annih_map_transpose (mat_treeSpace A 4) (Submodule.mem_map_of_mem wa)
  have a0 : mat A.transpose w=0 := pre _ wt (fun _ hi => transpose_tail_zero ha supportEnd hi)
  have d : diag (reflectedClock A) w=(1-nodes A j) • w := by
    ext i
    by_cases e : w i=0
    · simp [e]
    · simp [reflectedClock,on i e]
  let U : Submodule K (Fin 12 → K) := Submodule.span K {w}
  have aw : U≤annih (treeSpace A 5) := (Submodule.span_singleton_le_iff_mem ..).mpr wa
  have ⟨_,_,_,_,_,kill⟩ := orderNine_rank_five_full ha ho rank
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

/-- Even signed affine coordinates at one clock cannot interpolate the
next physical grade-five evaluation row. -/
theorem order9_forbid_same_clock_interpolation
    {A : Matrix (Fin 12) (Fin 12) K} {b w : Fin 12 → K} {j : Fin 12}
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder A b 9)
    (rank : finrank K (treeSpace A 5)=10)
    (pre : IndependentBefore (treeSpace A 4) j)
    (prev : ∀ i, j ≤ i → w i=0)
    (clock : ∀ i, w i≠0 → nodes A i=nodes A j)
    (fit : ∀ v∈treeSpace A 5, v j=row w v) : False := by
  let q := coordinate (K:=K) j-w
  have qj : q j=1 := by simp [q,coordinate,prev j le_rfl]
  have qn : q≠0 := by intro e; rw [e] at qj; exact zero_ne_one qj
  have qr : q∈annih (treeSpace A 5) := by
    apply mem_annih.mpr
    intro v hv
    have e : row (coordinate j) v=v j := by
      rw [row_apply,dotProduct_comm,←row_apply,row_coordinate]
    change (coordinate (K:=K) j-w) ⬝ᵥ v=0
    rw [sub_dotProduct,←row_apply,←row_apply,e,fit _ hv,sub_self]
  apply order9_no_causal_clock_contrast ha ho rank pre qr qn
  · intro i hi
    simp [q,coordinate,ne_of_gt hi,prev i hi.le]
  · intro i hi
    by_cases e : i=j
    · simp [e]
    · apply clock i
      intro z
      apply hi
      simp [q,coordinate,e,z]

end RKResearch.Certified.Graded.OneOff
