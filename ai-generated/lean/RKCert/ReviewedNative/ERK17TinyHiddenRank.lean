module

public import RKCert.ReviewedNative.ERKGradeEightSurplus
public import RKCert.ReviewedNative.LocalHiddenMomentBridge
public import RKCert.ReviewedNative.LocalLinearQuarticSeven
public import RKCert.ReviewedNative.FiveHiddenHead

@[expose] public section

/-! # The width-26 tiny-reverse hidden algebra and next rank

The rank-five case reuses the existing native five-dimensional
staircase. This does not exclude the rank-four or rank-five cases. -/
namespace RKResearch.Certified.ERK17
open RKResearch Module Polynomial Graded Graded.Reverse Graded.Reverse.LocalLinear
open RKCert.Endpoint RKCert.Endpoint.WeightedClock RKCert.OneEscape
open scoped Classical Matrix
noncomputable section

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A : Matrix (Fin 26) (Fin 26) K} {b τ : Fin 26→K}
variable {r : ℕ} {U : Submodule K (Fin 26→K)}

set_option maxRecDepth 3500
set_option maxHeartbeats 750000

theorem width26_tiny_first_seed_local_frame
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 17 A b)
    (nz : firstSeed A b≠0) (tiny : (weightedSites (reflectedClock A) (firstSeed A b)).card≤2) :
    ∃ r U τ, LocalLinearBand A b 7 r U τ ∧
      primitiveBack A b 7=annih (treeSpace A 8) := by
  have S := (ordered_width26_full_frame ha ho).1
  have rank (n : ℕ) (hn : n≤7) : finrank K (primitiveBack A b n)=n+1 := by
    obtain ⟨e,eq⟩ := S.reverse.flagExact n hn
    rw [←eq,e,first_dim_one nz]
  obtain ⟨r,U,τ,F⟩ := local_linear_band_of_paid_ranks (by decide : 3≤7) nz tiny rank
    (fun _ lo hi=>width26_reverse_clock_escape ha ho S lo hi)
  exact ⟨r,U,τ,F,(S.reverse.flagExact 7 (by decide)).2.symm.trans (S.reverse.firstNonzero nz)⟩

theorem width26_nonzero_forward_nine
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 17 A b) (nz : firstSeed A b≠0) :
    zeroSpace A 9=zeroSpace A 8⊔(zeroSpace A 8).map (diag (nodes A)) ∧
      finrank K (zeroSpace A 9)=10 := by
  have S := (ordered_width26_full_frame ha ho).1
  have f8 : finrank K (zeroSpace A 8)=9 := S.middleDefects
  have cap : finrank K (zeroSpace A 9)≤10 := by
    have e := S.nextRoom
    change finrank K (zeroSpace A 9)+finrank K (back A b 0)≤11 at e
    rw [first_dim_one nz] at e
    omega
  have sep := PolySeparated.of_coeff S.separated
  have esc : ¬(zeroSpace A 8).map (diag (nodes A))≤zeroSpace A 8 := by
    intro stable
    have e := clock_invariant_outgoing ha sep (U:=zeroSpace A 8) le_rfl stable
    change finrank K (zeroSpace A 8)+4≤finrank K (zeroSpace A 9) at e
    omega
  have move : (zeroSpace A 8).map (diag (nodes A))≤zeroSpace A 9 :=
    Submodule.map_le_iff_le_comap.mpr (diag_zeroSpace A 8)
  have step : zeroSpace A 8<zeroSpace A 9 :=
    lt_of_le_of_ne (zeroSpace_mono A (by decide)) (fun e=>esc (move.trans e.ge))
  have lower := Submodule.finrank_lt_finrank_of_lt step
  change finrank K (zeroSpace A 8)<finrank K (zeroSpace A 9) at lower
  have unit : finrank K (zeroSpace A (8 + 1)) = finrank K (zeroSpace A 8) + 1 := by
    change finrank K (zeroSpace A 9) = finrank K (zeroSpace A 8) + 1
    omega
  exact ⟨zeroSpace_clock_step_of_unit (n:=8) unit.le esc,by omega⟩

private theorem tiny_causal_mat (ha : ∀ i j,i≤j → A i j=0) : StrictlyCausal (mat A) := by
  intro i u v pre
  have e := causal_mat ha i (u-v) (fun j hj=>sub_eq_zero.mpr (pre j hj))
  simpa only [map_sub,Pi.sub_apply,sub_eq_zero] using e

private theorem weighted_one_eq_eval (P : K[X]) :
    weightedEval (nodes A) 1 P=evalNodes A P := by ext i; simp

/-- The genuine product-closed kernel contains `F4`, is contained in `F8`,
and has dimension four or five; no higher-grade blindness is assumed. -/
theorem width26_tiny_hidden_rank
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 17 A b) (nz : firstSeed A b≠0)
    (F : LocalLinearBand A b 7 r U τ)
    (full : primitiveBack A b 7=annih (treeSpace A 8)) :
    let J := hiddenKernel b τ U
    zeroSpace A 4≤J ∧ J≤zeroSpace A 8 ∧
      J.map (diag (nodes A))≤J ∧
      finrank K (zeroSpace A 3)+2≤finrank K J ∧ 4≤finrank K J ∧ finrank K J≤5 := by
  let J := hiddenKernel b τ U
  have rh : r≤7 := by rcases F.coreRank with e|e <;> omega
  have j4 : zeroSpace A 4≤J := grade_four_le_hiddenKernel_at_seven ha ho F full (by decide)
  have j8 : J≤zeroSpace A 8 := hiddenKernel_le_paid_defect ho F rh full (by decide)
  have clock : J.map (diag (nodes A))≤J := hiddenKernel_forward_clock_of_band F
  have S := (ordered_width26_full_frame ha ho).1
  have sep := PolySeparated.of_coeff S.separated
  have hm := clock_mask_invariant (fun _ hv=>clock (Submodule.mem_map_of_mem hv))
  have paid : finrank K (zeroSpace A 3)+2≤finrank K J := by
    apply incoming_nodal_gain (nodes A) 1 (zeroSpace A 3) J (mat A) (tiny_causal_mat ha)
      hm ((zeroSpace_mono A (by decide : 3≤4)).trans j4)
      (fun _ hz=>j4 (mat_zeroSpace_charZero A 3 hz)) 2
    · exact (by decide : 2≤8).trans (failed_nodes_of_separation sep j8 hm)
    · intro P hP
      rw [weighted_one_eq_eval,weighted_one_eq_eval,formalPrimitive_eq_native]
      exact j4 (primitive_defect A P (q:=3) (by omega))
  have low : 2≤finrank K (zeroSpace A 3) := zeroSpace_finrank ha ho (n:=2) (by decide)
  have cap : finrank K (zeroSpace A 9)≤11 := by
    rw [(width26_nonzero_forward_nine ha ho nz).2]
    decide
  have hi : finrank K J≤5 := invariant_core_cap_of_rank (q:=8) ha (by decide)
    S.separated S.middleDefects cap J j8 clock
  exact ⟨j4,j8,clock,paid, (Nat.add_le_add_right low 2).trans paid,hi⟩

theorem width26_tiny_rank_five_head
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 17 A b) (nz : firstSeed A b≠0)
    (F : LocalLinearBand A b 7 r U τ)
    (full : primitiveBack A b 7=annih (treeSpace A 8))
    (rank : finrank K (hiddenKernel b τ U)=5) :
    ∃ w, FiveHiddenStaircase A 8 (hiddenKernel b τ U) w ∧
      zeroSpace A 9=chain (diag (nodes A)) (hiddenKernel b τ U) w 5 := by
  have S := (ordered_width26_full_frame ha ho).1
  have r9 := width26_nonzero_forward_nine ha ho nz
  have cap : finrank K (zeroSpace A 9)≤11 := by rw [r9.2]; decide
  have rh : r≤7 := by rcases F.coreRank with e|e <;> omega
  have inside := hiddenKernel_le_paid_defect ho F rh full (by decide)
  have clock := hiddenKernel_forward_clock_of_band F
  obtain ⟨w,H⟩ := five_hidden_staircase ha (by decide : 8≤8) S.separated S.middleDefects cap rank inside clock
  have mid : zeroSpace A 8=chain (diag (nodes A)) (hiddenKernel b τ U) w 4 := H.midpoint
  have next := r9.1
  rw [mid,clock_chain_next clock (by decide : 0<4)] at next
  exact ⟨w,H,next⟩

end
end RKResearch.Certified.ERK17
