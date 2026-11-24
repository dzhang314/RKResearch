module

public import RKCert.ReviewedNative.ERK19LocalFirstFrame
public import RKCert.ReviewedNative.LocalLinearHiddenKernel
public import RKCert.ReviewedNative.ForwardInvariantCap

@[expose] public section

/-! # Actual rank-four or rank-five hidden algebra in the remaining ERK19 branch -/
namespace RKResearch.Certified.ERK19
open RKResearch Module Polynomial Graded Graded.Reverse Graded.Reverse.LocalLinear RKCert.Endpoint
open scoped Classical Matrix
noncomputable section
variable {K : Type*} [Field K]
variable {A : Matrix (Fin 29) (Fin 29) K} {b : Fin 29→K}
variable {r : ℕ} {U : Submodule K (Fin 29→K)} {τ : Fin 29→K}

theorem hiddenKernel_le_midpoint (ho : HasOrder 19 A b) (F : LocalLinearBand A b 8 r U τ)
    (full : primitiveBack A b 8=annih (treeSpace A 9)) :
    hiddenKernel b τ U≤zeroSpace A 9 := by
  intro v hv
  apply eval_alias_from_full_probes ho (by decide) (hiddenKernel_le_midpoint_tree F full hv)
  intro k
  have prod : b*v∈U := (mem_hiddenKernel.mp hv).2.1
  have inside : U≤primitiveBack A b 8 := F.core.le.trans
    ((monotone_nat_of_le_succ (adjointFlag_le_succ _)) (by rcases F.coreRank with w|w <;> omega))
  have ph : (X^k.val : K[X]).natDegree≤9 := by rw [natDegree_X_pow]; exact Nat.le_of_lt_succ k.isLt
  have test := mem_annih.mp (full.le (inside prod)) _ (evalNodes_mem_treeSpace A _ ph)
  rw [row_apply,dotProduct] at test
  simp only [probe,row_apply,dotProduct]
  convert test using 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.mul_apply,evalNodes_apply,eval_pow,eval_X]
  ring

private theorem hidden_causal_mat (ha : ∀ i j,i≤j→A i j=0) : StrictlyCausal (mat A) := by
  intro i u v pre
  have e := causal_mat ha i (u-v) (fun j hj=>sub_eq_zero.mpr (pre j hj))
  simpa only [map_sub,Pi.sub_apply,sub_eq_zero] using e

private theorem weighted_const_eq_eval (P : K[X]) :
    weightedEval (nodes A) 1 P=evalNodes A P := by ext i; simp

variable [LinearOrder K] [IsStrictOrderedRing K]

theorem width29_local_hidden_rank (ha : ∀ i j,i≤j→A i j=0) (ho : HasOrder 19 A b)
    (nz : firstSeed A b≠0) (F : LocalLinearBand A b 8 r U τ)
    (full : primitiveBack A b 8=annih (treeSpace A 9)) :
    4≤finrank K (hiddenKernel b τ U) ∧ finrank K (hiddenKernel b τ U)≤5 := by
  let J := hiddenKernel b τ U
  have j4 : zeroSpace A 4≤J := grade_four_le_hiddenKernel ha ho F full (by decide)
  have j9 : J≤zeroSpace A 9 := hiddenKernel_le_midpoint ho F full
  have clock : J.map (diag (nodes A))≤J := hiddenKernel_forward_clock F
  have hm := clock_mask_invariant (fun _ hv=>clock (Submodule.mem_map_of_mem hv))
  have hgain : finrank K (zeroSpace A 3)+2≤finrank K J := by
    apply incoming_nodal_gain (nodes A) 1 (zeroSpace A 3) J (mat A) (hidden_causal_mat ha)
      hm ((zeroSpace_mono A (by decide : 3≤4)).trans j4)
      (fun _ hz=>j4 (mat_zeroSpace_charZero A 3 hz)) 2
    · exact paid_failed_clock_blocks ho (by decide) j9 hm (by decide)
    · intro P hP
      rw [weighted_const_eq_eval,weighted_const_eq_eval,formalPrimitive_eq_native]
      exact j4 (primitive_defect A P (q:=3) (by omega))
  have lo : 2≤finrank K (zeroSpace A 3) := zeroSpace_finrank ha ho (n:=2) (by decide)
  have fr := (ordered_width29_frame ha ho).1
  have ten := (nonzero_seed_grade_ten ha ho nz).1
  have hi : finrank K J≤5 := invariant_core_cap_of_rank (q:=9) ha (by decide)
    fr.separated fr.middleDefects (by change finrank K (zeroSpace A 10)≤12; omega) J j9 clock
  change 4≤finrank K J ∧ finrank K J≤5
  exact ⟨by omega,hi⟩

/-- A nonzero seed now leaves only a coordinatewise kernel of genuine
dimension four or five; no hypothesis on the small support is added. -/
theorem width29_nonzero_small_hidden_rank (ha : ∀ i j,i≤j→A i j=0) (ho : HasOrder 19 A b)
    (nz : firstSeed A b≠0) :
    ∃ r U τ, LocalLinearBand A b 8 r U τ ∧ primitiveBack A b 8=annih (treeSpace A 9) ∧
      zeroSpace A 4≤hiddenKernel b τ U ∧ hiddenKernel b τ U≤zeroSpace A 9 ∧
      4≤finrank K (hiddenKernel b τ U) ∧ finrank K (hiddenKernel b τ U)≤5 := by
  obtain ⟨r,U,τ,F,full,_⟩ := width29_nonzero_local_first_frame ha ho nz
  obtain ⟨lo,hi⟩ := width29_local_hidden_rank ha ho nz F full
  exact ⟨r,U,τ,F,full,grade_four_le_hiddenKernel ha ho F full (by decide),
    hiddenKernel_le_midpoint ho F full,lo,hi⟩

end
end RKResearch.Certified.ERK19
