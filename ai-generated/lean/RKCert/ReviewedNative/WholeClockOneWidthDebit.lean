module

public import RKCert.ReviewedNative.ClockOneLiveSuffix
public import RKCert.ReviewedNative.ClockOneCompensatedRank
public import RKCert.ReviewedNative.EffectiveDonorClocks
import RKCert.ReviewedNative.EndpointKernelNormalization
import RKCert.ReviewedNative.ForwardNodalGain
import RKCert.ReviewedNative.NativeFlatClockHead
import RKCert.ReviewedNative.ERKGradeFiveSurplus
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Native width debit of a whole clock-one group in a live suffix

The zero first seed, the full ordinary reverse annihilator equality and
the whole live-group chronology are actual hypotheses. This result never
moves a stage, drops a nonzero weight or assumes individual positivity. -/
namespace RKResearch.Certified.Graded.Reverse

open RKResearch Polynomial Module
open RKResearch.Certified.Graded.EffectiveDonors
open scoped Matrix BigOperators Classical

noncomputable section

variable {K : Type*} [Field K] {s n p : ℕ}
variable {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : Fin (s+1) → K}
variable {u : Fin (s+1)}

/-- Among original output-live stages, the cut selects exactly clock one. -/
def WholeLiveClockOneSuffix (A : Matrix (Fin (s+1)) (Fin (s+1)) K)
    (b : Fin (s+1) → K) (u : Fin (s+1)) : Prop :=
  ∀ i, b i ≠ 0 → (u ≤ i ↔ nodes A i = 1)

private theorem sum_suffix_eq_whole_clockMass
    (whole : WholeLiveClockOneSuffix A b u) :
    (∑ i ∈ suffixLiveStages b u, b i) = clockMass (nodes A) b 1 := by
  classical
  rw [suffixLiveStages, Finset.sum_filter, clockMass]
  apply Finset.sum_congr rfl
  intro i _
  by_cases bi : b i = 0
  · simp [bi]
  · by_cases ui : u ≤ i
    · have ci : nodes A i = 1 := (whole i bi).mp ui
      simp [ui, bi, ci]
    · have ci : nodes A i ≠ 1 := fun atOne => ui ((whole i bi).mpr atOne)
      simp [ui, bi, ci]

section Ordered
variable [LinearOrder K] [IsStrictOrderedRing K]

/-- Measured and ordinary width debits. Here q=n+1, W=q+1+dim L_(q−2),
k is the number of original live clock-one rows, and loss is one exactly
for the tuned signed mass 1/(q(q+1)). The separate hinge charges one
extra direction when the effective rank k−loss is below floor(q/2). -/
theorem full_whole_clock_one_suffix_width_debit
    (ha : ∀ i r, i ≤ r → A i r = 0) (ho : HasOrder p A b)
    (n1 : 1 ≤ n) (pay : 2*(n+1) ≤ p) (first : firstSeed A b = 0)
    (full : primitiveBack A b (n-1) = annih (treeSpace A (n+1)))
    (whole : WholeLiveClockOneSuffix A b u) :
    let W := n+2 + finrank K (primitiveBack A b (n-1))
    let k := (suffixLiveStages b u).card
    let μ := clockMass (nodes A) b 1
    let loss : ℕ := if (((n : K)+1)*((n : K)+2))*μ = 1 then 1 else 0
    let bonus : ℕ := if k < (n+1)/2+loss then 1 else 0
    (W+finrank K (clockOneLowerSpan A n)+k ≤ s+1+loss) ∧
    (W+finrank K (zeroSpace A n)+k+bonus ≤ s+1+loss) ∧
    (5 ≤ n → 3*(n+1)-2+k+bonus ≤ s+1+loss) ∧
    (5 ≤ n → μ = 0 → 3*(n+1)+1 ≤ s+1) ∧
    (7 ≤ n → μ = 0 → s+1 ≤ 3*(n+1)+1 →
      s+1 = 3*(n+1)+1 ∧ k = 2 ∧
      finrank K (primitiveBack A b (n-1)) = n-1 ∧ finrank K (zeroSpace A n) = n ∧
      finrank K (clockOneLowerSpan A n) = n+1 ∧ finrank K (zeroSpace A (n+1)) = n+3) := by
  classical
  let L := primitiveBack A b (n-1)
  let F := zeroSpace A n
  let Fplus := zeroSpace A (n+1)
  let U := clockOneLowerSpan A n
  let W := n+2+finrank K L
  let S := suffixLiveStages b u
  let k := S.card
  let μ := clockMass (nodes A) b 1
  let κ : K := ((n : K)+1)*((n : K)+2)
  let loss : ℕ := if κ*μ = 1 then 1 else 0
  let bonus : ℕ := if k < (n+1)/2+loss then 1 else 0
  change (W+finrank K U+k ≤ s+1+loss) ∧
    (W+finrank K F+k+bonus ≤ s+1+loss) ∧
    (5 ≤ n → 3*(n+1)-2+k+bonus ≤ s+1+loss) ∧
    (5 ≤ n → μ = 0 → 3*(n+1)+1 ≤ s+1) ∧
    (7 ≤ n → μ = 0 → s+1 ≤ 3*(n+1)+1 →
      s+1 = 3*(n+1)+1 ∧ k = 2 ∧ finrank K L = n-1 ∧
      finrank K F = n ∧ finrank K U = n+1 ∧ finrank K Fplus = n+3)
  have one (i : Fin (s+1)) (ui : u ≤ i) (bi : b i ≠ 0) : nodes A i = 1 :=
    (whole i bi).mp ui
  obtain ⟨t, last⟩ := exists_lastActive ho (by omega)
  have tmem : t ∈ S :=
    mem_suffixLiveStages.mpr ⟨(whole t last.live).mpr (last.node_eq_one ha first), last.live⟩
  have inh : Nonempty S := ⟨⟨t, tmem⟩⟩
  let σ : S → Fin (s+1) := fun i => i.val
  have inj : Function.Injective σ := fun _ _ h => Subtype.ext h
  have props (i : S) :
      nodes A (σ i) = 1 ∧ b (σ i) ≠ 0 ∧ coordinate (K := K) (σ i) ∈ treeSpace A (n+1) :=
    live_clock_one_suffix_coordinate ha first one full i.property
  obtain ⟨R, Rd, _, kernel, fullDebit, shortDebit⟩ :=
    clock_one_compensated_rank ha ho pay σ inj inh
      (fun i => (props i).1) (fun i => (props i).2.1) (fun i => (props i).2.2)
  have value : R.eval 1 = κ :=
    unit_X_reproducer_eval_one R Rd
      (fun H Hd => by simpa only [clockOneUnitMass_apply] using kernel H Hd)
  have masseq : (∑ i : S, b (σ i)) = μ := by
    change (∑ i : S, b i.val) = μ
    rw [Finset.sum_coe_sort]
    exact sum_suffix_eq_whole_clockMass whole
  have rankDebit : finrank K U+k ≤ finrank K Fplus+loss := by
    by_cases tune : κ*μ = 1
    · have z : R.eval 1 * (∑ i : S, b (σ i)) = 1 := by
        rw [value, masseq]
        exact tune
      have d := shortDebit z
      rw [Fintype.card_coe] at d
      rw [show loss = 1 from if_pos tune]
      exact d
    · have z : R.eval 1 * (∑ i : S, b (σ i)) ≠ 1 := by
        rw [value, masseq]
        exact tune
      have d := fullDebit z
      rw [Fintype.card_coe] at d
      simp only [show loss = 0 from if_neg tune, Nat.add_zero]
      exact d
  have ordinary := explicit_midpoint_rank_eq ha ho (q := n+1) (by omega) pay
  have dims := finrank_annih (treeSpace A (n+1))
  rw [← full, ordinary, Fintype.card_fin] at dims
  have width : W+finrank K Fplus = s+1 := by
    dsimp only [W, L, Fplus]
    omega
  have measured : W+finrank K U+k ≤ s+1+loss := by omega
  have inc : F ≤ U := le_sup_left
  have fU := Submodule.finrank_mono inc
  have coeffSep := explicit_coeff_separated ha ho (q := n) (by omega)
  have hermite (stable : F.map (diag (nodes A)) ≤ F) :
      finrank K F+(n+1)/2 ≤ finrank K Fplus :=
    clock_invariant_outgoing ha (PolySeparated.of_coeff coeffSep) (U := F) le_rfl stable
  have clockJump (escape : ¬ F.map (diag (nodes A)) ≤ F) :
      finrank K F < finrank K U := by
    apply Submodule.finrank_lt_finrank_of_lt
    refine lt_of_le_of_ne inc (fun e => escape ?_)
    exact (show F.map (diag (nodes A)) ≤ U from le_sup_right).trans (le_of_eq e.symm)
  have hinge : W+finrank K F+k+bonus ≤ s+1+loss := by
    by_cases below : k < (n+1)/2+loss
    · rw [show bonus = 1 from if_pos below]
      by_cases stable : F.map (diag (nodes A)) ≤ F
      · have rise := hermite stable
        omega
      · have jump := clockJump stable
        omega
    · rw [show bonus = 0 from if_neg below]
      omega
  have fLow (n5 : 5 ≤ n) : n ≤ finrank K F := by
    have early := grade_five_surplus_of_reviewed_order ha ho (by omega : 10 ≤ p)
    have growth := zeroSpace_rank_interval_of_separation ha coeffSep
      (j := 5) (d := n-5) (by omega) (by omega)
    rw [show 5+(n-5) = n by omega] at growth
    change n ≤ finrank K (zeroSpace A n)
    omega
  have rLow : n-1 ≤ finrank K L := by
    have rr := back_finrank ha ho (n-1) (by omega)
    rw [first_dim_zero first, zero_add] at rr
    exact rr.trans (Submodule.finrank_mono (back_le_primitiveBack (A := A) (b := b) (n-1)))
  have absolute (n5 : 5 ≤ n) : 3*(n+1)-2+k+bonus ≤ s+1+loss := by
    have fmin := fLow n5
    dsimp only [W] at hinge
    omega
  have untuned (hm : μ = 0) : loss = 0 := by
    change (if κ*μ = 1 then (1 : ℕ) else 0) = 0
    apply if_neg
    rw [hm, mul_zero]
    exact zero_ne_one
  have cancellationTwo (hm : μ = 0) : 2 ≤ k := by
    have kp : 0 < k := Finset.card_pos.mpr ⟨t, tmem⟩
    by_contra no
    have k1 : S.card = 1 := by change k = 1; omega
    obtain ⟨i, si⟩ := Finset.card_eq_one.mp k1
    have imem : i ∈ S := by simp [si]
    have bi : b i ≠ 0 := (mem_suffixLiveStages.mp imem).2
    have z : (∑ i ∈ S, b i) = 0 := (sum_suffix_eq_whole_clockMass whole).trans hm
    rw [si, Finset.sum_singleton] at z
    exact bi z
  have minCancelled (n5 : 5 ≤ n) (hm : μ = 0) : 3*(n+1)+1 ≤ s+1 := by
    have k2 := cancellationTwo hm
    have h := absolute n5
    have e := untuned hm
    rw [e, Nat.add_zero] at h
    by_cases exactlyTwo : k = 2
    · have belowCut : k < (n+1)/2+loss := by rw [e]; omega
      have b1 : bonus = 1 := if_pos belowCut
      omega
    · omega
  refine ⟨measured, hinge, absolute, minCancelled, ?_⟩
  intro n7 hm cap
  have n5 : 5 ≤ n := by omega
  have se : s+1 = 3*(n+1)+1 := Nat.le_antisymm cap (minCancelled n5 hm)
  have k2 := cancellationTwo hm
  have h := absolute n5
  have e := untuned hm
  rw [e, Nat.add_zero] at h
  have exactTwo : k = 2 := by
    by_contra neq
    have k3 : k = 3 := by omega
    have belowCut : k < (n+1)/2+loss := by rw [e]; omega
    have b1 : bonus = 1 := if_pos belowCut
    omega
  have belowCut : k < (n+1)/2+loss := by rw [e]; omega
  have b1 : bonus = 1 := if_pos belowCut
  have fmin := fLow n5
  have sharp : W+finrank K F+k+bonus ≤ s+1+loss := hinge
  dsimp only [W] at sharp width
  have rExact : finrank K L = n-1 := by omega
  have fExact : finrank K F = n := by omega
  have qExact : finrank K Fplus = n+3 := by omega
  have escape : ¬ F.map (diag (nodes A)) ≤ F := by
    intro stable
    have rise := hermite stable
    omega
  have jump := clockJump escape
  have uExact : finrank K U = n+1 := by omega
  exact ⟨se, exactTwo, rExact, fExact, uExact, qExact⟩

end Ordered
end
end RKResearch.Certified.Graded.Reverse
