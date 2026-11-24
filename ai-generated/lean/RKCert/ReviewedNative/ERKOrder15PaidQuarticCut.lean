module

public import RKCert.ReviewedNative.ERKOrder15RankTwoChart

@[expose] public section

/-! # The very same knot argument at the rank-two, grade-four seam

The only added premise is a physical degree-four head profile already
paid in grade four. This file does not assert that such a profile has
been extracted from an arbitrary rank-two chart. -/
namespace RKResearch.Certified.Graded

open RKResearch Reverse Polynomial RKCert.OneEscape RKCert.Endpoint
open scoped Classical
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {s a : ℕ}
variable {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : Fin (s+1)→K}
variable {G P : K[X]} {w : Fin (s+1)→K} {U : Submodule K (Fin (s+1)→K)}

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem marked_clock_step (j : ℕ) :
    markedDefectSpace A b j≤(markedDefectSpace A b (j+1)).comap (diag (nodes A)) := by
  apply Submodule.map_le_iff_le_comap.mp
  change (zeroSpace A j⊔terminalMark A b).map (diag (nodes A))≤_
  rw [Submodule.map_sup]
  exact sup_le_sup (Submodule.map_le_iff_le_comap.mpr (diag_zeroSpace A j)) (terminalMark_clock A b)

/-- A genuine rank-two quartic head paid in grade four forces the actual
terminal mark and grade-eight entry over ordered fields. Both omissions
and all five scalar tests reuse the shared physical construction. -/
theorem Order15PaidStaircase.terminal_of_paid_quartic (S : Order15PaidStaircase A b a G 2 U w)
    (ha : ∀ i t,i≤t → A i t=0) (ho : HasOrder A b 15)
    (w4 : w∈markedDefectSpace A b 4)
    (dis : ∀ i, LiveCore.live U i → w i=0)
    (repr : ∀ i, w i≠0 → w i=P.eval (nodes A i))
    (pn : P≠0) (pd : P.natDegree≤4) :
    firstSeed A b=0 ∧ coordinate (K:=K) (Fin.last s)∈treeSpace A 8 := by
  by_contra absent
  have out : firstSeed A b≠0 ∨ coordinate (K:=K) (Fin.last s)∉treeSpace A 8 := by
    by_cases h : firstSeed A b=0
    · exact Or.inr (fun z => absent ⟨h,z⟩)
    · exact Or.inl h
  have base := order15_absent_terminal_grade_eight_rigid ha ho S out
  have next : markedDefectSpace A b 8=chain (diag (nodes A)) U w 5 := by
    change zeroSpace A 8⊔terminalMark A b=_
    rw [base]
    exact S.escape
  have closed (u : Fin (s+1)→K) (hu : u∈U) (v : Fin (s+1)→K) (hv : v∈U) :
      u*v∈U := S.core_times_five ha ho (S.earlyCore hv) hu
  have core : U≤markedDefectSpace A b 7 :=
    S.earlyCore.trans (sup_le_sup (zeroSpace_mono A (by decide)) le_rfl)
  have sep : ∀ F : K[X], F.natDegree≤7 → evalNodes A F∈markedDefectSpace A b 7 → F=0 :=
    eval_eq_zero_of_coeff_separated (marked_coeff_separated ha ho S.frame.lastActive
      (by have := S.frame.size; omega) (q:=7) (j:=7) (by decide) (by decide))
  have powers (k : ℕ) : (diag (nodes A)^k) w∈markedDefectSpace A b (4+k) := by
    induction k with
    | zero => simpa using w4
    | succ k ih =>
      rw [pow_succ',Module.End.mul_eq_comp,LinearMap.comp_apply]
      exact marked_clock_step _ ih
  have paid (R : K[X]) (d : R.natDegree≤3) :
      weightedEval (nodes A) w R∈markedDefectSpace A b 7 :=
    weighted_eval_mem_of_powers
      (fun k hk => (sup_le_sup (zeroSpace_mono A (by omega : 4+k≤7)) le_rfl) (powers k)) R d
  have moves : markedDefectSpace A b 7≤(chain (diag (nodes A)) U w 5).comap (mat A) := by
    rw [←next]
    exact marked_defect_mat ha 7
  have defects : zeroSpace A 8≤chain (diag (nodes A)) U w 5 := by
    rw [←next]
    exact le_sup_left
  obtain ⟨i,t,B⟩ := physical_head_knots_three_two
    (physical_head_knot (j:=7) (N:=5) ha S.stable closed dis repr pn (by omega)
      core paid sep moves defects (S.escape ▸ S.first.paid))
  exact pn (RKCert.EndpointPhysical.ordered_quartic_eq_zero_of_primitives pd B.firstNonzero
    B.secondNonzero B.different ⟨B.firstTest,B.secondTest⟩)

end RKResearch.Certified.Graded
