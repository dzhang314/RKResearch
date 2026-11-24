module

public import RKCert.ReviewedNative.TwoSeedRank
public import RKCert.ReviewedNative.GradedDefects
public import RKCert.ReviewedNative.DIRKSeedReduction

public section

/-! # Native DIRK forward-rank gain with both actual seeds

Only the checked reviewed tree-order predicate and graded defect spaces
are used. No characteristic-zero, distinct-node, or nonzero diagonal
assumption is needed. The forcing theorem is imported, not repeated. -/
namespace RKResearch.Certified.Graded
open Module
open scoped Matrix

variable {K : Type*} [Field K] {s p : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}

private theorem nodes_not_in_paid_zeroSpace (ho : HasOrder A b p)
    {j : ℕ} (pay : j+1≤p) (paidNode : 2≤p) : nodes A∉zeroSpace A j := by
  intro hn
  have zero := probe_zeroSpace (j:=j) (k:=0) ho (by omega) hn
  change probe A b 0 (nodes A)=0 at zero
  have normalized : normTree A (clockTree 1)=nodes A := by
    simpa using normTree_clockTree A 1
  have paid := probe_normTree ho (clockTree 1) 0 (by simpa using paidNode)
  rw [normalized,zero,mul_zero] at paid
  exact zero_ne_one paid

/-- A true DIRK defect flag cannot stall after degree two at a paid level.
The index (j+1) is paid; no moment assumption at (j+2) is used. -/
theorem dirk_forward_zeroSpace_lt_succ (ha : A.IsLowerTriangular) (ho : HasOrder A b p)
    {j : ℕ} (hj : 2≤j) (pay : j+1≤p) :
    zeroSpace A j < zeroSpace A (j+1) := by
  apply RKCert.ReviewedNative.RankFlags.strict_of_two_seed_forcing
      (N:=mat A) (D:=diag (nodes A))
      (q₂:=monomialStageDefect A 1) (q₃:=monomialStageDefect A 2) (target:=nodes A)
  · exact zeroSpace_mono A (Nat.le_succ _)
  · exact mat_zeroSpace ho j pay
  · exact diag_zeroSpace A j
  · exact zeroSpace_mono A (by omega : 2≤j+1) (monomialStageDefect_mem A 1)
  · exact zeroSpace_mono A (by omega : 3≤j+1) (monomialStageDefect_mem A 2)
  · exact nodes_not_in_paid_zeroSpace ho pay (by omega)
  · exact forward_dirk_seeds_force_nodes ha

theorem dirk_forward_zeroSpace_rank_floor (ha : A.IsLowerTriangular) (ho : HasOrder A b p)
    {q : ℕ} (hq : 2≤q) (pay : q≤p) :
    q-2≤finrank K (zeroSpace A q) ∧
      (monomialStageDefect A 1≠0 → q-1≤finrank K (zeroSpace A q)) := by
  have gain := RKCert.ReviewedNative.RankFlags.finrank_gain_of_steps (zeroSpace A) hq
    (fun j hj jq => dirk_forward_zeroSpace_lt_succ ha ho hj (by omega))
  refine ⟨by omega, ?_⟩
  intro nz
  have pos : 0<finrank K (zeroSpace A 2) := by
    by_contra notPos
    have eq : zeroSpace A 2=⊥ := Submodule.finrank_eq_zero.mp (by omega)
    apply nz
    have mem := monomialStageDefect_mem A 1
    change monomialStageDefect A 1∈zeroSpace A 2 at mem
    rwa [eq, Submodule.mem_bot] at mem
  omega

/-- Exact grade-three forward lower ranks required by the native p15
rank budget: one always, an additional direction when the quadratic
stage defect does not vanish. -/
theorem dirk_forward_rank_three (ha : A.IsLowerTriangular) (ho : HasOrder A b p)
    (pay : 3≤p) : 1≤finrank K (zeroSpace A 3) ∧
      (monomialStageDefect A 1≠0 → 2≤finrank K (zeroSpace A 3)) := by
  simpa using dirk_forward_zeroSpace_rank_floor ha ho (q:=3) (by decide) pay

end RKResearch.Certified.Graded

#print axioms RKCert.ReviewedNative.RankFlags.strict_of_two_seed_forcing
#print axioms RKCert.ReviewedNative.RankFlags.finrank_gain_of_steps
#print axioms RKResearch.Certified.Graded.dirk_forward_zeroSpace_lt_succ
#print axioms RKResearch.Certified.Graded.dirk_forward_rank_three
