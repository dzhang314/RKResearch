module

public import RKCert.ReviewedNative.NativeFlatClockHead
public import RKCert.ReviewedNative.NativeHeadMultiplier
public import RKCert.ReviewedNative.ERKGradeFiveSurplus

@[expose] public section

/-! # Native geometry forced by a small grade-eight defect space

These consequences hold at every stage count and already at order 16.
The separated remaining obligations are the grade-four quartic branch,
the grade-three multiplier contrast, and the rank-three intrinsic core. -/
namespace RKResearch.Certified.Graded
open RKResearch Polynomial Module RKCert.OneEscape RKCert.Endpoint
open scoped Classical

variable {K : Type*} [Field K] [CharZero K] {s p : ℕ}
variable {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : Fin (s+1) → K}

theorem grade_eight_thin_head (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder A b p) (pay : 16≤p)
    (cap : finrank K (zeroSpace A 8) ≤ 8) :
    ∃ r U w, 2≤r ∧ finrank K (zeroSpace A 5)=5 ∧ FlatClockHead A 5 3 r U w := by
  have sep := explicit_coeff_separated ha ho (q:=8) pay
  have low := grade_five_surplus_of_reviewed_order ha ho (by omega)
  obtain ⟨r,U,w,H⟩ := flat_clock_head ha (j:=5) (d:=3) sep (by decide) (by decide)
    (show finrank K (zeroSpace A 8) ≤ finrank K (zeroSpace A 5)+3 by omega)
  have d8 := H.ranks 3 (by decide)
  change finrank K (zeroSpace A 8) = finrank K (zeroSpace A 5)+3 at d8
  have d5 : finrank K (zeroSpace A 5)=5 := by omega
  have d6 := H.ranks 1 (by decide)
  change finrank K (zeroSpace A 6) = finrank K (zeroSpace A 5)+1 at d6
  have sep8 : PolySeparated A 8 := PolySeparated.of_coeff sep
  have gain := clock_invariant_outgoing ha (sep8.mono (show 5≤8 by decide)) H.coreInside H.coreStable
  change finrank K U+3 ≤ finrank K (zeroSpace A 6) at gain
  have base := H.baseRank
  exact ⟨r,U,w,by omega,d5,H⟩

/-- The grade-four exceptional branch is also a genuine flat chart,
or else the fourth defect space has its smallest possible rank three. -/
theorem grade_eight_grade_four_split (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder A b p)
    (pay : 16≤p) (cap : finrank K (zeroSpace A 8) ≤ 8) :
    finrank K (zeroSpace A 4)=3 ∨
      (finrank K (zeroSpace A 4)=4 ∧ ∃ r U w, FlatClockHead A 4 4 r U w) := by
  have sep := explicit_coeff_separated ha ho (q:=8) pay
  have low : 3 ≤ finrank K (zeroSpace A 4) := zeroSpace_finrank ha ho (n:=3) (by omega)
  have high := zeroSpace_rank_interval_of_separation ha sep (j:=4) (d:=4) (by decide) (by decide)
  change finrank K (zeroSpace A 4)+4 ≤ finrank K (zeroSpace A 8) at high
  by_cases e : finrank K (zeroSpace A 4)=3
  · exact Or.inl e
  · have dim : finrank K (zeroSpace A 4)=4 := by omega
    exact Or.inr ⟨dim,flat_clock_head ha (j:=4) (d:=4) sep (by decide) (by decide)
      (show finrank K (zeroSpace A 8) ≤ finrank K (zeroSpace A 4)+4 by omega)⟩

set_option maxRecDepth 2600 in
set_option maxHeartbeats 650000 in
omit [CharZero K] in
/-- An actual third-grade vector outside the intrinsic core has a nonzero
cubic multiplier profile. Its pointwise multiplication preserves the
core, with no independent block or generic clock assumption. -/
theorem grade_eight_grade_three_profile {r : ℕ} {U : Submodule K (Fin (s+1)→K)}
    {w v : Fin (s+1)→K} (H : FlatClockHead A 5 3 r U w)
    (hv : v∈zeroSpace A 3) (outside : v∉U) :
    U.map (diag v) ≤ U ∧ ∃ P : K[X], P≠0 ∧ P.natDegree≤3 ∧
      v*w-weightedEval (nodes A) w P∈U := by
  have F5 : zeroSpace A 5 = chain (diag (nodes A)) U w r := by simpa only [Nat.add_zero] using H.flags 0 (by decide)
  have F8 : zeroSpace A 8 = chain (diag (nodes A)) U w (r+3) := H.flags 3 (by decide)
  have mulStable : U.map (diag v) ≤ U := by
    rintro _ ⟨u,hu,rfl⟩
    have hh : zeroSpace A (5+3) ≤ chain (diag (nodes A)) U w (r+3) := F8.le
    have h : u*v ∈ U :=
      HeadFiber.core_mul (A:=A) (j:=5) (k:=3) H.coreStable H.coreInside H.extraSites hh hu hv
    have eq : diag v u = u*v := by ext i; simp [mul_comm]
    exact eq.symm ▸ h
  have v5 : v∈chain (diag (nodes A)) U w r := F5 ▸ (zeroSpace_mono A (by decide : 3≤5) hv)
  have band (k : ℕ) (hk : k<r) :
      v*((diag (nodes A)^k) w)∈chain (diag (nodes A)) U w (r+3) := by
    rw [←F8]
    have h := (clock_chain_le_iff r).mp F5.ge
    exact zeroSpace_mul (A:=A) (m:=3) (n:=5) hv (h.2 k hk)
  obtain ⟨P,nz,d,eq⟩ := HeadFiber.multiplier_profile_of_chart H.coreStable mulStable H.extraSites H.positive band v5 outside
  exact ⟨mulStable,P,nz,by omega,eq⟩

/-- If the third grade already lies in the core and the fourth has rank
three, the core is precisely the fourth-grade space. -/
theorem grade_eight_core_eq_grade_four (ha : ∀ i j, i≤j → A i j=0)
    (ho : HasOrder A b p) (pay : 16≤p) {r : ℕ} {U : Submodule K (Fin (s+1)→K)}
    {w : Fin (s+1)→K} (H : FlatClockHead A 5 3 r U w)
    (r2 : 2≤r) (f5 : finrank K (zeroSpace A 5)=5)
    (f4 : finrank K (zeroSpace A 4)=3) (inside : zeroSpace A 3 ≤ U) :
    zeroSpace A 4 = U := by
  have sep := explicit_coeff_separated ha ho (q:=8) pay
  have low : 2 ≤ finrank K (zeroSpace A 3) := zeroSpace_finrank ha ho (n:=2) (by omega)
  have hi := zeroSpace_rank_interval_of_separation ha sep (j:=3) (d:=1) (by decide) (by decide)
  change finrank K (zeroSpace A 3)+1 ≤ finrank K (zeroSpace A 4) at hi
  have f3 : finrank K (zeroSpace A 3)=2 := by omega
  have sep8 : PolySeparated A 8 := PolySeparated.of_coeff sep
  have esc : ¬(zeroSpace A 3).map (diag (nodes A)) ≤ zeroSpace A 3 := by
    intro inv
    have g := clock_invariant_outgoing ha (sep8.mono (show 3≤8 by decide)) le_rfl inv
    change finrank K (zeroSpace A 3)+2 ≤ finrank K (zeroSpace A 4) at g
    omega
  have step := zeroSpace_clock_step_of_unit (n:=3) (A:=A)
    (show finrank K (zeroSpace A 4)≤finrank K (zeroSpace A 3)+1 by omega) esc
  have sub : zeroSpace A 4 ≤ U := by
    rw [step]
    exact sup_le inside ((Submodule.map_mono inside).trans H.coreStable)
  have r := H.baseRank
  exact Submodule.eq_of_le_of_finrank_le sub (by omega)

end RKResearch.Certified.Graded
