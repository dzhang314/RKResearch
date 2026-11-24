module

public import RKCert.ReviewedNative.NativeClockStaircase
import RKCert.ReviewedNative.ERKCharZero

@[expose] public section

/-! # Two live unequal clocks force the genuine quadratic escape

The line test is independent of tableau order and causality. Its grade
three application uses the actual defect and only two forward rank caps.
-/
namespace RKResearch.Certified.Graded

open RKResearch Module RKCert.OneEscape
open RKResearch.Certified.Graded.Reverse
noncomputable section

section Line
variable {ι K : Type*} [Fintype ι] [Field K]

/-- A literal line escapes the clock exactly when its defining vector is
nonzero at two original coordinates carrying different clock values. -/
theorem clock_line_escape_iff_two_live_clocks (c g : ι→K) :
    (¬ ((K ∙ g : Submodule K (ι→K)).map (diag c) ≤ K ∙ g)) ↔
      ∃ i j, g i≠0 ∧ g j≠0 ∧ c i≠c j := by
  classical
  let U : Submodule K (ι→K) := K ∙ g
  change (¬ (U.map (diag c) ≤ U)) ↔ _
  have gU : g∈U := Submodule.mem_span_singleton_self g
  constructor
  · intro escape
    by_contra no
    apply escape
    apply Submodule.map_le_iff_le_comap.mpr
    change (K ∙ g : Submodule K (ι→K)) ≤ U.comap (diag c)
    rw [Submodule.span_singleton_le_iff_mem]
    change diag c g∈U
    by_cases live : ∃ i, g i≠0
    · obtain ⟨i,hi⟩ := live
      have eq : diag c g=c i • g := by
        ext j
        by_cases hj : g j=0
        · simp only [diag_apply,Pi.smul_apply,smul_eq_mul,hj,mul_zero]
        · have cj : c j=c i := by
            by_contra ne
            exact no ⟨j,i,hj,hi,ne⟩
          simp only [diag_apply,Pi.smul_apply,smul_eq_mul,cj]
      rw [eq]
      exact U.smul_mem _ gU
    · have g0 : g=0 := by
        ext i
        exact not_not.mp (fun h=>live ⟨i,h⟩)
      simpa only [g0,map_zero] using U.zero_mem
  · rintro ⟨i,j,hi,hj,distinct⟩ stable
    have pre : diag c g∈U.map (diag c) := Submodule.mem_map_of_mem gU
    have hg : diag c g∈(K ∙ g : Submodule K (ι→K)) := stable pre
    obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp hg
    have eq : diag c g=a • g := by first | exact ha | exact ha.symm
    have clock (k : ι) (hk : g k≠0) : c k=a := by
      have e : c k*g k=a*g k := by
        simpa only [diag_apply,Pi.smul_apply,smul_eq_mul] using congrFun eq k
      exact mul_right_cancel₀ hk e
    exact distinct ((clock i hi).trans (clock j hj).symm)

end Line

section Defect
variable {K : Type*} [Field K] {s : ℕ} {A : Matrix (Fin s) (Fin s) K}

/-- Two actual dirty clock values supply the previously missing grade
three chain, provided the genuine forward ranks have room one and two. -/
theorem grade_three_chain_of_two_quadratic_live_clocks
    (rankTwo : finrank K (zeroSpace A 2)≤1)
    (rankThree : finrank K (zeroSpace A 3)≤2)
    {i j : Fin s} (hi : monomialStageDefect A 1 i≠0)
    (hj : monomialStageDefect A 1 j≠0) (different : nodes A i≠nodes A j) :
    zeroSpace A 3=chain (diag (nodes A)) ⊥ (monomialStageDefect A 1) 2 := by
  let g := monomialStageDefect A 1
  let C := diag (nodes A)
  have gn : g≠0 := by
    intro hz
    have h : g i=0 := by rw [hz,Pi.zero_apply]
    exact hi h
  have gm : g∈zeroSpace A 2 := monomialStageDefect_mem A 1
  have sp : (K ∙ g : Submodule K (Fin s→K))≤zeroSpace A 2 := by
    rw [Submodule.span_singleton_le_iff_mem]
    exact gm
  have sb : (⊥ : Submodule K (Fin s→K)) < K ∙ g := by
    apply lt_of_le_of_ne bot_le
    intro e
    have h : g∈(K ∙ g : Submodule K (Fin s→K)) := Submodule.mem_span_singleton_self g
    rw [←e,Submodule.mem_bot] at h
    exact gn h
  have spanPos := Submodule.finrank_lt_finrank_of_lt sb
  rw [finrank_bot] at spanPos
  have rlo := Submodule.finrank_mono sp
  have line : zeroSpace A 2=K ∙ g :=
    (Submodule.eq_of_le_of_finrank_le sp (by omega)).symm
  have escape : ¬ ((zeroSpace A 2).map C≤zeroSpace A 2) := by
    rw [line]
    exact (clock_line_escape_iff_two_live_clocks (nodes A) g).mpr ⟨i,j,hi,hj,different⟩
  have unit : finrank K (zeroSpace A (2+1)) ≤ finrank K (zeroSpace A 2) + 1 := by
    change finrank K (zeroSpace A 3) ≤ finrank K (zeroSpace A 2) + 1
    omega
  have step := zeroSpace_clock_step_of_unit (A:=A) (n:=2) unit escape
  have base : zeroSpace A 2=chain C ⊥ g 1 := by
    simpa [chain,one_apply_eq_self] using line
  have botStable : (⊥ : Submodule K (Fin s→K)).map C≤⊥ := by simp
  calc
    zeroSpace A 3 = zeroSpace A 2 ⊔ (zeroSpace A 2).map C := step
    _ = chain C ⊥ g 1 ⊔ (chain C ⊥ g 1).map C := by rw [base]
    _ = chain C ⊥ g 2 := clock_chain_next botStable (by decide : 0<(1:ℕ))

variable [CharZero K] {b : Fin s→K} {p q : ℕ}

/-- Under paid minimal midpoint rank, the two unequal dirty clocks
supply precisely the conditional base used by the clean-row theorem. -/
theorem minimal_defect_baseF3_of_two_quadratic_live_clocks
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder p A b)
    (pay : 2*q≤p) (minimal : finrank K (zeroSpace A q)=q-1)
    {i j : Fin s} (hi : monomialStageDefect A 1 i≠0)
    (hj : monomialStageDefect A 1 j≠0) (different : nodes A i≠nodes A j) :
    3≤q → zeroSpace A 3=chain (diag (nodes A)) ⊥ (monomialStageDefect A 1) 2 := by
  intro q₃
  have r₂ := erk_paid_rank_interval ha ho (a:=2) (q:=q) (by decide) (by omega) pay
  have r₃ := erk_paid_rank_interval ha ho (a:=3) (q:=q) (by decide) q₃ pay
  exact grade_three_chain_of_two_quadratic_live_clocks (by omega) (by omega) hi hj different

end Defect

end
end RKResearch.Certified.Graded
