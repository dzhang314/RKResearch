module

public import RKCert.ReviewedNative.ERK19LocalHiddenRank
public import RKCert.ReviewedNative.LocalLinearDegreeDrop
public import RKCert.ReviewedNative.FiveHiddenHead

@[expose] public section

/-! Draft only: consume the existing generic five-invariant staircase at the
actual local nonzero order-19 midpoint. No new scalar certificate. -/
namespace RKResearch.Certified.ERK19
open RKResearch Module Polynomial Graded Graded.Reverse Graded.Reverse.LocalLinear
open RKCert.OneEscape
open scoped Classical
noncomputable section

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A : Matrix (Fin 29) (Fin 29) K} {b : Fin 29→K}
variable {r : ℕ} {U : Submodule K (Fin 29→K)} {τ : Fin 29→K}

structure LocalFiveGeometry (A : Matrix (Fin 29) (Fin 29) K) (b : Fin 29→K)
    (r : ℕ) (U : Submodule K (Fin 29→K)) (τ h : Fin 29→K) (P Q : K[X]) : Prop where
  staircase : FiveHiddenStaircase A 9 (hiddenKernel b τ U) h
  tenth : zeroSpace A 10=chain (diag (nodes A)) (hiddenKernel b τ U) h 6
  treeSevenRank : finrank K (treeSpace A 7)=16
  reverseCap : finrank K (primitiveBack A b 10)≤13
  fit : LocalLinearTraces A b U τ h r 5 P Q
  nonzeroHead : Q≠0

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem chain_dim_next (C : (Fin 29→K) →ₗ[K] Fin 29→K)
    (J : Submodule K (Fin 29→K)) (h : Fin 29→K) (n : ℕ) :
    finrank K (chain C J h (n+1))≤finrank K (chain C J h n)+1 := by
  let S := chain C J h n
  let w := (C^n) h
  change finrank K (S⊔Submodule.span K {w} : Submodule K (Fin 29→K))≤finrank K S+1
  by_cases sv : w∈S
  · have le : Submodule.span K ({w} : Set (Fin 29→K))≤S := by
      apply Submodule.span_le.mpr
      intro z hz
      exact (Set.mem_singleton_iff.mp hz).symm ▸ sv
    rw [sup_eq_left.mpr le]
    omega
  · rw [Submodule.finrank_sup_span_singleton sv]

set_option maxHeartbeats 550000 in
theorem width29_local_five_geometry
    (ha : ∀ i j,i≤j→A i j=0) (ho : HasOrder 19 A b) (nz : firstSeed A b≠0)
    (F : LocalLinearBand A b 8 r U τ) (full : primitiveBack A b 8=annih (treeSpace A 9))
    (rank : finrank K (hiddenKernel b τ U)=5) :
    ∃ h P Q, LocalFiveGeometry A b r U τ h P Q := by
  let J := hiddenKernel b τ U
  let C := diag (nodes A)
  have inc : J≤zeroSpace A 9 := hiddenKernel_le_midpoint ho F full
  have inv : J.map C≤J := hiddenKernel_forward_clock F
  have fr := (ordered_width29_frame ha ho).1
  have f10 := (nonzero_seed_grade_ten ha ho nz).1
  obtain ⟨h,S⟩ := five_hidden_staircase (q:=9) ha (by decide) fr.separated fr.middleDefects
    (by change finrank K (zeroSpace A 10)≤12; omega) rank inc inv
  have tenth : zeroSpace A 10=chain C J h 6 := by
    rw [nonzero_seed_grade_ten_clock_step ha ho nz,S.midpoint]
    change chain C J h 5⊔(chain C J h 5).map C=chain C J h 6
    exact clock_chain_next inv (by decide)
  have f7 : finrank K (zeroSpace A 7)=8 := by
    have ub := zeroSpace_rank_interval_of_separation ha fr.separated (j:=7) (d:=2) (by decide) (by decide)
    change finrank K (zeroSpace A 7)+2≤finrank K (zeroSpace A 9) at ub
    have j7 := S.flags 7 (by decide) (by decide)
    have j9 := S.midpoint
    change zeroSpace A 7=chain C J h 3 at j7
    change zeroSpace A 9=chain C J h 5 at j9
    have d3 := chain_dim_next C J h 3
    have d4 := chain_dim_next C J h 4
    change finrank K (chain C J h 4)≤finrank K (chain C J h 3)+1 at d3
    change finrank K (chain C J h 5)≤finrank K (chain C J h 4)+1 at d4
    rw [←j7] at d3
    rw [←j9,fr.middleDefects] at d4
    rw [fr.middleDefects] at ub
    omega
  have e7 := treeSpace_rank_eq_of_separation ho (q:=7) (by decide) (coeff_separated ho (by decide))
  rw [f7] at e7
  change finrank K (treeSpace A 7)=16 at e7
  have budget : finrank K (primitiveBack A b 10)≤13 := by
    have ct := finrank_annih (treeSpace A 7)
    have paid := Submodule.finrank_mono (primitiveBack_annih ho 7 10 (by decide))
    rw [e7,Fintype.card_fin] at ct
    omega
  have r2 : r≤2 := by rcases F.coreRank with h|h <;> omega
  obtain ⟨P,Q,S'⟩ := local_linear_two_traces ho F full (by decide) (by omega) S.headGrade
  exact ⟨h,P,Q,⟨S,tenth,e7,budget,S',fun eq=>S.outside (hiddenKernel_of_zero_head F S' eq)⟩⟩

end
end RKResearch.Certified.ERK19
