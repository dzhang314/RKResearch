module

public import RKCert.ReviewedNative.NativeClockStaircase
import RKCert.ReviewedNative.ERKCharZero
import RKCert.ReviewedNative.ForwardNodalGain

@[expose] public section

/-! # Minimal paid defect rank detects the genuine quadratic defect

The minimum rank is at one paid even midpoint. The grade-three base
must be supplied when it is in range; outgoing rank gain starts at k=3.
Width and reverse data are not used.
-/
namespace RKResearch.Certified.Graded

open RKResearch Module RKCert.OneEscape
open RKResearch.Certified.Graded.Reverse
noncomputable section

variable {K : Type*} [Field K] {s p q : ℕ}
    {A : Matrix (Fin s) (Fin s) K} {b : Fin s→K}

private theorem quadratic_seed_ne_of_separation
    (ha : ∀ i k, i≤k → A i k=0) (sep : PolySeparated A q) (hq : 1≤q) :
    monomialStageDefect A 1≠0 := by
  intro hz
  let B : Submodule K (Fin s→K) := ⊥
  have cv : diag (nodes A) (1 : Fin s→K)=nodes A := by ext i; simp
  have seed :
      (2:K) • mat A (diag (nodes A) 1)-diag (nodes A) (diag (nodes A) 1) =
        monomialStageDefect A 1 := by
    rw [cv]
    ext i
    simp [monomialStageDefect,pow_two]
  have hit : diag (nodes A) (1 : Fin s→K)∈B := by
    apply mem_of_invariant_seed (Equiv.refl _) (mat A) (causal_mat ha) (nodes A) 1 B
    · intro v hv
      have hv0 : v=0 := by simpa only [B,Submodule.mem_bot] using hv
      simpa only [hv0,map_zero] using B.zero_mem
    · intro v hv
      have hv0 : v=0 := by simpa only [B,Submodule.mem_bot] using hv
      simpa only [hv0,map_zero] using B.zero_mem
    · simpa only [seed,hz] using B.zero_mem
  have hc : nodes A∈B := cv ▸ hit
  have c0 : nodes A=0 := by simpa only [B,Submodule.mem_bot] using hc
  exact (sep.nodes_not_mem hq) (c0.symm ▸ (zeroSpace A q).zero_mem)

section CharacteristicZero
variable [CharZero K]

/-- Minimal actual rank propagates a supplied grade-three clock-chain
base. Grade two is proved directly, and no grade-three premise is
needed if the paid range stops at grade two. -/
theorem minimal_defect_clock_chain
    (ha : ∀ i k, i≤k → A i k=0) (ho : HasOrder p A b)
    (pay : 2*q≤p) (minimal : finrank K (zeroSpace A q)=q-1)
    (baseF3 : 3≤q → zeroSpace A 3=
      chain (diag (nodes A)) ⊥ (monomialStageDefect A 1) 2)
    {j : ℕ} (j₂ : 2≤j) (jq : j≤q) :
    zeroSpace A j =
      chain (diag (nodes A)) ⊥ (monomialStageDefect A 1) (j-1) := by
  have q₂ : 2≤q := j₂.trans jq
  have coeffSep : ∀ a, coeffEval A q a∈zeroSpace A q → a=0 := by
    cases s with
    | zero =>
      have stages := RKResearch.Certified.explicit_order_le_stages ha ho
      exact False.elim (by omega)
    | succ s => exact explicit_coeff_separated ha ho pay
  have sep : PolySeparated A q := PolySeparated.of_coeff coeffSep
  have ranks (k : ℕ) (k₂ : 2≤k) (kq : k≤q) :
      finrank K (zeroSpace A k)=k-1 := by
    have low := zeroSpace_finrank ha ho (n:=k-1) (by omega)
    rw [show k-1+1=k by omega] at low
    have high := erk_paid_rank_interval ha ho (a:=k) (q:=q) (by omega) kq pay
    omega
  let C := diag (nodes A)
  let g := monomialStageDefect A 1
  have gn : g≠0 := quadratic_seed_ne_of_separation ha sep (by omega)
  have base : zeroSpace A 2=chain C ⊥ g 1 := by
    have gm : g∈zeroSpace A 2 := monomialStageDefect_mem A 1
    have sp : (K ∙ g : Submodule K (Fin s→K))≤zeroSpace A 2 := by
      rw [Submodule.span_singleton_le_iff_mem]
      exact gm
    have notBot : (⊥ : Submodule K (Fin s→K)) < K ∙ g := by
      apply lt_of_le_of_ne bot_le
      intro e
      have h : g∈(K ∙ g : Submodule K (Fin s→K)) := Submodule.mem_span_singleton_self g
      rw [←e,Submodule.mem_bot] at h
      exact gn h
    have spanRank := Submodule.finrank_lt_finrank_of_lt notBot
    rw [finrank_bot] at spanRank
    have rankTwo := ranks 2 (by decide) q₂
    have equal := Submodule.eq_of_le_of_finrank_le sp (by omega)
    simpa [chain,one_apply_eq_self] using equal.symm
  have step (k : ℕ) (k₃ : 3≤k) (kq : k+1≤q) :
      zeroSpace A (k+1)=zeroSpace A k ⊔ (zeroSpace A k).map C := by
    have r := ranks k (by omega) (by omega)
    have r' := ranks (k+1) (by omega) kq
    apply zeroSpace_clock_step_of_unit (A:=A) (n:=k) (by omega)
    intro invariant
    have kSep : PolySeparated A k := sep.mono (by omega)
    have gain := clock_invariant_outgoing ha kSep (U:=zeroSpace A k) le_rfl invariant
    omega
  have botStable : (⊥ : Submodule K (Fin s→K)).map C≤⊥ := by simp
  have chainAt (n : ℕ) (nq : n+3≤q) :
      zeroSpace A (n+3)=chain C ⊥ g (n+2) := by
    induction n with
    | zero => exact baseF3 (by omega)
    | succ n ih =>
      change zeroSpace A (n+3+1)=chain C ⊥ g (n+2+1)
      rw [step (n+3) (by omega) (by omega),ih (by omega)]
      exact clock_chain_next botStable (by omega)
  by_cases jBase : j=2
  · subst j
    exact base
  have h := chainAt (j-3) (by omega)
  rwa [show j-3+3=j by omega,show j-3+2=j-1 by omega] at h

end CharacteristicZero

/-- A clock chain from the actual quadratic defect is clean at a row
exactly when that seed vanishes there. This consumer needs only the
chain equality and the genuine grade-two membership. -/
theorem clean_iff_quadratic_zero_of_clock_chain {j n : ℕ} (j₂ : 2≤j)
    (hchain : zeroSpace A j =
      chain (diag (nodes A)) ⊥ (monomialStageDefect A 1) n) (i : Fin s) :
    (∀ f∈zeroSpace A j, f i=0) ↔ monomialStageDefect A 1 i=0 := by
  constructor
  · intro clean
    exact clean _ (zeroSpace_mono A j₂ (monomialStageDefect_mem A 1))
  · intro qzero
    have powers (k : ℕ) : ((diag (nodes A))^k) (monomialStageDefect A 1) i=0 := by
      induction k with
      | zero => simpa only [pow_zero,one_apply_eq_self] using qzero
      | succ k ih =>
        rw [pow_succ',Module.End.mul_eq_comp,LinearMap.comp_apply,diag_apply,ih,mul_zero]
    have vanishing :
        chain (diag (nodes A)) ⊥ (monomialStageDefect A 1) n ≤
          (LinearMap.proj i).ker := by
      refine (clock_chain_le_iff n).mpr ⟨bot_le,?_⟩
      intro k _
      exact powers k
    intro f hf
    exact vanishing (hchain ▸ hf)

/-- Clean-row criterion through the paid minimal midpoint, conditional on
the grade-three base if in range. No terminal or site-count premise. -/
theorem minimal_defect_clean_iff_quadratic_zero [CharZero K]
    (ha : ∀ i k, i≤k → A i k=0) (ho : HasOrder p A b)
    (pay : 2*q≤p) (minimal : finrank K (zeroSpace A q)=q-1)
    (baseF3 : 3≤q → zeroSpace A 3=
      chain (diag (nodes A)) ⊥ (monomialStageDefect A 1) 2)
    {j : ℕ} (j₂ : 2≤j) (jq : j≤q) (i : Fin s) :
    (∀ f∈zeroSpace A j, f i=0) ↔ monomialStageDefect A 1 i=0 :=
  clean_iff_quadratic_zero_of_clock_chain j₂ (minimal_defect_clock_chain ha ho pay minimal baseF3 j₂ jq) i

end
end RKResearch.Certified.Graded
