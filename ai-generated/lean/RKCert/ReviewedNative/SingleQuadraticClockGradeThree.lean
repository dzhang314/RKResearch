module

public import RKCert.ReviewedNative.GradedGrowth
import RKCert.ReviewedNative.ERKCharZero

@[expose] public section

/-! # A single live quadratic clock forces the actual A-advance

A clock-stable quadratic line cannot also be causally invariant while it
excludes the ordinary clock column. In a rank-two grade three the actual
quadratic defect and its A-advance are therefore the two generators.
-/
namespace RKResearch.Certified.Graded

open RKResearch Module
open RKResearch.Certified.Graded.Reverse
noncomputable section

section Lines
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

private theorem map_line_le_of_apply_mem {T : V→ₗ[K] V} {g : V}
    (h : T g∈(K ∙ g : Submodule K V)) : (K ∙ g : Submodule K V).map T≤K ∙ g := by
  apply Submodule.map_le_iff_le_comap.mpr
  rw [Submodule.span_singleton_le_iff_mem]
  exact h

end Lines

section CleanSupport
variable {K ι : Type*} [Field K] {U : Submodule K (ι→K)} {u v : ι→K}

/-- Cleanliness of a literal two-vector span is exactly the intersection
of its two pointwise vanishing loci. -/
theorem clean_iff_two_vector_span
    (shape : U=(K ∙ u : Submodule K (ι→K)) ⊔ K ∙ v) (i : ι) :
    (∀ f∈U, f i=0) ↔ u i=0 ∧ v i=0 := by
  constructor
  · intro h
    have hu : u∈U := by
      rw [shape]
      exact (show (K ∙ u : Submodule K (ι → K)) ≤ K ∙ u ⊔ K ∙ v from le_sup_left) (Submodule.mem_span_singleton_self u)
    have hv : v∈U := by
      rw [shape]
      exact (show (K ∙ v : Submodule K (ι → K)) ≤ K ∙ u ⊔ K ∙ v from le_sup_right) (Submodule.mem_span_singleton_self v)
    exact ⟨h u hu,h v hv⟩
  · rintro ⟨hu,hv⟩
    have uK : (K ∙ u : Submodule K (ι→K))≤(LinearMap.proj i).ker := by
      rw [Submodule.span_singleton_le_iff_mem]
      exact hu
    have vK : (K ∙ v : Submodule K (ι→K))≤(LinearMap.proj i).ker := by
      rw [Submodule.span_singleton_le_iff_mem]
      exact hv
    have inK : U≤(LinearMap.proj i).ker := by rw [shape]; exact sup_le uK vK
    intro f hf
    exact inK hf

end CleanSupport

section Quadratic
variable {K : Type*} [Field K] {s p : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s→K}

/-- A common clock on the nonzero support preserves the actual
quadratic-defect line, regardless of the signs of the entries. -/
theorem quadratic_line_clock_stable_of_single_live_clock (a : K)
    (single : ∀ i, monomialStageDefect A 1 i≠0 → nodes A i=a) :
    (K ∙ monomialStageDefect A 1 : Submodule K (Fin s→K)).map (diag (nodes A)) ≤
      K ∙ monomialStageDefect A 1 := by
  classical
  let g := monomialStageDefect A 1
  change (K ∙ g : Submodule K (Fin s→K)).map (diag (nodes A))≤K ∙ g
  apply map_line_le_of_apply_mem
  have eq : diag (nodes A) g=a • g := by
    ext i
    by_cases z : g i=0
    · simp only [diag_apply,Pi.smul_apply,smul_eq_mul,z,mul_zero]
    · simp only [diag_apply,Pi.smul_apply,smul_eq_mul,single i z]
  rw [eq]
  exact (K ∙ g : Submodule K (Fin s→K)).smul_mem a (Submodule.mem_span_singleton_self _)

/-- No order or rank is used here. The causal seed identity would put
the clock column in the line if the actual A-advance were also in it. -/
theorem mat_quadratic_defect_outside_clock_stable_line
    (ha : ∀ i j, i≤j → A i j=0)
    (clockOut : nodes A∉(K ∙ monomialStageDefect A 1 : Submodule K (Fin s→K)))
    (stable : (K ∙ monomialStageDefect A 1 : Submodule K (Fin s→K)).map
      (diag (nodes A))≤K ∙ monomialStageDefect A 1) :
    mat A (monomialStageDefect A 1)∉(K ∙ monomialStageDefect A 1 : Submodule K (Fin s→K)) := by
  let g := monomialStageDefect A 1
  let U : Submodule K (Fin s→K) := K ∙ g
  intro adv
  have forward : U.map (mat A)≤U := map_line_le_of_apply_mem adv
  have cv : diag (nodes A) (1 : Fin s→K)=nodes A := by ext i; simp
  have seed : (2:K) • mat A (diag (nodes A) 1)-diag (nodes A) (diag (nodes A) 1)=g := by
    rw [cv]
    ext i
    simp [g,monomialStageDefect,pow_two]
  have hit : diag (nodes A) (1 : Fin s→K)∈U := by
    apply mem_of_invariant_seed (Equiv.refl _) (mat A) (causal_mat ha) (nodes A) 1 U
    · intro v hv
      exact forward (Submodule.mem_map_of_mem hv)
    · intro v hv
      exact stable (Submodule.mem_map_of_mem hv)
    · rw [seed]
      exact Submodule.mem_span_singleton_self _
  exact clockOut (cv ▸ hit)

/-- A typed rank-two alternative to the two unequal-clock branch. -/
structure SingleQuadraticClockGradeThree (A : Matrix (Fin s) (Fin s) K) : Prop where
  independent : mat A (monomialStageDefect A 1)∉
    (K ∙ monomialStageDefect A 1 : Submodule K (Fin s→K))
  shape : zeroSpace A 3=(K ∙ monomialStageDefect A 1 : Submodule K (Fin s→K)) ⊔
    K ∙ (mat A (monomialStageDefect A 1))
  clean : ∀ i : Fin s, (∀ f∈zeroSpace A 3, f i=0) ↔
    monomialStageDefect A 1 i=0 ∧ mat A (monomialStageDefect A 1) i=0

/-- One live quadratic clock forces a second actual independent seed
A g. The only rank premise is an upper cap of two at grade three. -/
theorem grade_three_of_single_quadratic_live_clock
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder p A b) (pay : 3≤p)
    (rankThird : finrank K (zeroSpace A 3)≤2) (a : K)
    (single : ∀ i, monomialStageDefect A 1 i≠0 → nodes A i=a) :
    SingleQuadraticClockGradeThree A := by
  let g := monomialStageDefect A 1
  let h := mat A g
  let U : Submodule K (Fin s→K) := K ∙ g
  have gm : g∈zeroSpace A 2 := monomialStageDefect_mem A 1
  have gU : g∈U := Submodule.mem_span_singleton_self _
  have line₂ : U≤zeroSpace A 2 := by
    dsimp only [U]
    rw [Submodule.span_singleton_le_iff_mem]
    exact gm
  have clockOut : nodes A∉zeroSpace A 2 := by
    intro c
    have z : probe A b 0 (nodes A)=0 := probe_zeroSpace ho (by omega) c
    have m : ((2:ℕ):K)*probe A b 0 (nodes A)=1 := by
      simpa only [probe,row_apply,pow_zero,mul_one,pow_one] using
        ho.hasQuadratureOrder 1 (by omega)
    rw [z,mul_zero] at m
    exact zero_ne_one m
  have sep : h∉U := mat_quadratic_defect_outside_clock_stable_line ha
    (fun u => clockOut (line₂ u)) (quadratic_line_clock_stable_of_single_live_clock a single)
  have hm : h∈zeroSpace A 3 := mat_zeroSpace ho 2 (show 2+1≤p from pay) gm
  have gn : g≠0 := by
    intro z
    exact sep (by simpa only [h,z,map_zero] using U.zero_mem)
  have inF : U ⊔ K ∙ h≤zeroSpace A 3 := by
    apply sup_le (line₂.trans (zeroSpace_mono A (by decide : 2≤3)))
    rw [Submodule.span_singleton_le_iff_mem]
    exact hm
  have start : (⊥ : Submodule K (Fin s→K))<U := by
    apply lt_of_le_of_ne bot_le
    intro e
    have h := gU
    rw [←e,Submodule.mem_bot] at h
    exact gn h
  have grow : U<U ⊔ K ∙ h := by
    apply lt_of_le_of_ne le_sup_left
    intro e
    have hmem : h∈U ⊔ K ∙ h := (show (K ∙ h : Submodule K (Fin s → K)) ≤ U ⊔ K ∙ h from le_sup_right) (Submodule.mem_span_singleton_self h)
    rw [←e] at hmem
    exact sep hmem
  have one := Submodule.finrank_lt_finrank_of_lt start
  rw [finrank_bot] at one
  have two := Submodule.finrank_lt_finrank_of_lt grow
  have shape : zeroSpace A 3=U ⊔ K ∙ h :=
    (Submodule.eq_of_le_of_finrank_le inF (by omega)).symm
  exact ⟨sep,shape,fun i=>clean_iff_two_vector_span shape i⟩

/-- In the paid minimal rank family, the checked interval bound supplies
the grade-three cap, without any statement about the number of stages. -/
theorem minimal_grade_three_of_single_quadratic_live_clock [CharZero K] {q : ℕ}
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder p A b)
    (q₃ : 3≤q) (pay : 2*q≤p) (minimal : finrank K (zeroSpace A q)=q-1)
    (a : K) (single : ∀ i, monomialStageDefect A 1 i≠0 → nodes A i=a) :
    SingleQuadraticClockGradeThree A := by
  have r := erk_paid_rank_interval ha ho (a:=3) (q:=q) (by decide) q₃ pay
  exact grade_three_of_single_quadratic_live_clock ha ho (by omega) (by omega) a single

end Quadratic

end
end RKResearch.Certified.Graded
