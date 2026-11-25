module

public import RKCert.ReviewedNative.NativeClockStaircase
public import RKCert.ReviewedNative.SingleQuadraticClockGradeThree
import RKCert.ReviewedNative.ERKCharZero
import RKCert.ReviewedNative.ForwardNodalGain
import RKCert.ReviewedNative.MinimalDefectClean
import RKCert.ReviewedNative.QuadraticClockEscape

@[expose] public section

/-! # The paid minimal defect tail and its two actual clean probes

The two-clock and singleton-clock bases are different. In the singleton
case the invariant line is retained and the actual A-advance generates
the growing clock orbit. Both cases give the same two-vector zero test.
-/
namespace RKResearch.Certified.Graded

open RKResearch Module RKCert.OneEscape
open RKResearch.Certified.Graded.Reverse
noncomputable section

section ChainClean
variable {K ι : Type*} [Field K] [Fintype ι]
variable {c u v : ι→K} {n : ℕ}

/-- Pointwise cleanliness of a retained line and a nonempty clock orbit
amounts to two literal zero tests, without any rank or order premise. -/
theorem clean_iff_line_clock_chain (nonempty : 0<n) (i : ι) :
    (∀ f∈chain (diag c) (K ∙ u) v n, f i=0) ↔ u i=0 ∧ v i=0 := by
  constructor
  · intro clean
    have pay := (clock_chain_le_iff (T:=diag c) (U:=K ∙ u) (w:=v) n).mp le_rfl
    have uc : u∈chain (diag c) (K ∙ u) v n :=
      pay.1 (Submodule.mem_span_singleton_self u)
    have vc : v∈chain (diag c) (K ∙ u) v n := by
      simpa only [pow_zero,one_apply_eq_self] using pay.2 0 nonempty
    exact ⟨clean u uc,clean v vc⟩
  · rintro ⟨uz,vz⟩
    have line : (K ∙ u : Submodule K (ι→K))≤(LinearMap.proj i).ker := by
      rw [Submodule.span_singleton_le_iff_mem]
      exact uz
    have orbit (k : ℕ) : ((diag c)^k) v i=0 := by
      induction k with
      | zero => simpa only [pow_zero,one_apply_eq_self] using vz
      | succ k ih =>
        rw [pow_succ',Module.End.mul_eq_comp,LinearMap.comp_apply,diag_apply,ih,mul_zero]
    have inc : chain (diag c) (K ∙ u) v n≤(LinearMap.proj i).ker :=
      (clock_chain_le_iff n).mpr ⟨line,fun k _=>orbit k⟩
    intro f hf
    exact inc hf

end ChainClean

section PaidTail
variable {K : Type*} [Field K] [CharZero K] {s p q : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s→K}

/-- Any actual grade-three head over a stable base propagates through a
paid minimal-rank tail. The outgoing gain is used only above grade two. -/
theorem minimal_defect_clock_tail_of_grade_three
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder p A b)
    (pay : 2*q≤p) (minimal : finrank K (zeroSpace A q)=q-1)
    {U : Submodule K (Fin s→K)} {w : Fin s→K}
    (stable : U.map (diag (nodes A))≤U)
    (base : zeroSpace A 3=chain (diag (nodes A)) U w 1)
    {j : ℕ} (j₃ : 3≤j) (jq : j≤q) :
    zeroSpace A j=chain (diag (nodes A)) U w (j-2) := by
  have q₃ : 3≤q := j₃.trans jq
  have coeffSep : ∀ a, coeffEval A q a∈zeroSpace A q → a=0 := by
    cases s with
    | zero =>
      have stages := RKResearch.Certified.explicit_order_le_stages ha ho
      exact False.elim (by omega)
    | succ s => exact explicit_coeff_separated ha ho pay
  have sep : PolySeparated A q := PolySeparated.of_coeff coeffSep
  have ranks (k : ℕ) (k₃ : 3≤k) (kq : k≤q) :
      finrank K (zeroSpace A k)=k-1 := by
    have low := zeroSpace_finrank ha ho (n:=k-1) (by omega)
    rw [show k-1+1=k by omega] at low
    have high := erk_paid_rank_interval ha ho (a:=k) (q:=q) (by omega) kq pay
    omega
  let C := diag (nodes A)
  have step (k : ℕ) (k₃ : 3≤k) (kq : k+1≤q) :
      zeroSpace A (k+1)=zeroSpace A k ⊔ (zeroSpace A k).map C := by
    have r := ranks k k₃ (by omega)
    have r' := ranks (k+1) (by omega) kq
    apply zeroSpace_clock_step_of_unit (A:=A) (n:=k) (by omega)
    intro invariant
    have kSep : PolySeparated A k := sep.mono (by omega)
    have gain := clock_invariant_outgoing ha kSep (U:=zeroSpace A k) le_rfl invariant
    omega
  have chainAt (n : ℕ) (nq : n+3≤q) :
      zeroSpace A (n+3)=chain C U w (n+1) := by
    induction n with
    | zero => exact base
    | succ n ih =>
      change zeroSpace A (n+3+1)=chain C U w (n+1+1)
      rw [step (n+3) (by omega) (by omega),ih (by omega)]
      exact clock_chain_next stable (by omega)
  have h := chainAt (j-3) (by omega)
  rwa [show j-3+3=j by omega,show j-3+1=j-2 by omega] at h

/-- The singleton-clock tail retains the actual quadratic line and
grows the clock orbit of the independent actual A-advance. -/
theorem minimal_defect_clock_tail_of_single_quadratic_live_clock
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder p A b)
    (pay : 2*q≤p) (minimal : finrank K (zeroSpace A q)=q-1)
    (a : K) (single : ∀ i, monomialStageDefect A 1 i≠0 → nodes A i=a)
    {j : ℕ} (j₃ : 3≤j) (jq : j≤q) :
    zeroSpace A j=chain (diag (nodes A)) (K ∙ monomialStageDefect A 1)
      (mat A (monomialStageDefect A 1)) (j-2) := by
  have T := minimal_grade_three_of_single_quadratic_live_clock ha ho (j₃.trans jq)
    pay minimal a single
  have base : zeroSpace A 3=chain (diag (nodes A)) (K ∙ monomialStageDefect A 1)
      (mat A (monomialStageDefect A 1)) 1 := by
    simpa [chain,one_apply_eq_self] using T.shape
  exact minimal_defect_clock_tail_of_grade_three ha ho pay minimal
    (quadratic_line_clock_stable_of_single_live_clock a single) base j₃ jq

theorem minimal_defect_clean_iff_of_single_quadratic_live_clock
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder p A b)
    (pay : 2*q≤p) (minimal : finrank K (zeroSpace A q)=q-1)
    (a : K) (single : ∀ i, monomialStageDefect A 1 i≠0 → nodes A i=a)
    {j : ℕ} (j₃ : 3≤j) (jq : j≤q) (i : Fin s) :
    (∀ f∈zeroSpace A j, f i=0) ↔
      monomialStageDefect A 1 i=0 ∧ mat A (monomialStageDefect A 1) i=0 := by
  rw [minimal_defect_clock_tail_of_single_quadratic_live_clock ha ho pay minimal a single j₃ jq]
  exact clean_iff_line_clock_chain (n:=j-2) (by omega) i

/-- At every paid minimal grade at least three, the clean rows are
exactly the common zeros of the actual quadratic defect and its A-advance.
A split on two unequal live clocks supplies the base internally; no common
one-seed clock-chain claim is made. -/
theorem minimal_defect_clean_iff_two_actual_seeds
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder p A b)
    (pay : 2*q≤p) (minimal : finrank K (zeroSpace A q)=q-1)
    {j : ℕ} (j₃ : 3≤j) (jq : j≤q) (i : Fin s) :
    (∀ f∈zeroSpace A j, f i=0) ↔
      monomialStageDefect A 1 i=0 ∧ mat A (monomialStageDefect A 1) i=0 := by
  classical
  constructor
  · intro clean
    have g₂ := monomialStageDefect_mem A 1
    have paidThree : 2+1≤p := by omega
    have h₃ : mat A (monomialStageDefect A 1)∈zeroSpace A 3 :=
      mat_zeroSpace ho 2 paidThree g₂
    exact ⟨clean _ (zeroSpace_mono A (by omega : 2≤j) g₂),
      clean _ (zeroSpace_mono A j₃ h₃)⟩
  · intro both
    by_cases unequal : ∃ r t : Fin s, monomialStageDefect A 1 r≠0 ∧
        monomialStageDefect A 1 t≠0 ∧ nodes A r≠nodes A t
    · obtain ⟨r,t,hr,ht,diff⟩ := unequal
      have base := minimal_defect_baseF3_of_two_quadratic_live_clocks ha ho pay minimal
        hr ht diff
      exact (minimal_defect_clean_iff_quadratic_zero (j:=j) ha ho pay minimal
        base (by omega) jq i).mpr both.1
    · have oneClock : ∃ a : K, ∀ k, monomialStageDefect A 1 k≠0 → nodes A k=a := by
        by_cases live : ∃ r : Fin s, monomialStageDefect A 1 r≠0
        · obtain ⟨r,hr⟩ := live
          refine ⟨nodes A r,fun k hk=>?_⟩
          by_contra different
          exact unequal ⟨k,r,hk,hr,different⟩
        · exact ⟨0,fun k hk=>(live ⟨k,hk⟩).elim⟩
      obtain ⟨a,single⟩ := oneClock
      exact (minimal_defect_clean_iff_of_single_quadratic_live_clock ha ho pay minimal
        a single j₃ jq i).mpr both

end PaidTail

end
end RKResearch.Certified.Graded
