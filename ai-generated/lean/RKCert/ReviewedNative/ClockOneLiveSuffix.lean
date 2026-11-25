module

public import RKCert.ReviewedNative.EndpointAdjoint

@[expose] public section

/-! # Literal coordinate membership for an actual clock-one live suffix

The chronology is the original Fin order. The cut permits any physical
zero-output row, regardless of its clock. The first reverse seed is zero;
every other actual monomial credit vanishes from the cut onward. A full
ordinary annihilator, not a terminal-deleted one, recovers the coordinates. -/
namespace RKResearch.Certified.Graded.Reverse

open RKResearch Module
open scoped Matrix

noncomputable section

variable {K : Type*} [Field K] {s : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}

/-- Exactly the nonzero physical weights from the original cut onward. -/
def suffixLiveStages (b : Fin s → K) (u : Fin s) : Finset (Fin s) := by
  classical
  exact Finset.univ.filter (fun i => u ≤ i ∧ b i ≠ 0)

@[simp] theorem mem_suffixLiveStages {i u : Fin s} :
    i ∈ suffixLiveStages b u ↔ u ≤ i ∧ b i ≠ 0 := by
  classical
  simp only [suffixLiveStages, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The last live row is always an eligible, nonempty suffix in the
strict explicit zero-first-seed case. A wider suffix needs its own clock test. -/
theorem LastActive.eligible_clock_one_suffix {u : Fin s} (L : LastActive b u)
    (ha : ∀ i r, i ≤ r → A i r = 0) (first : firstSeed A b = 0) :
    (suffixLiveStages b u).Nonempty ∧
      (∀ i, u ≤ i → b i ≠ 0 → nodes A i = 1) := by
  refine ⟨⟨u, mem_suffixLiveStages.mpr ⟨le_rfl, L.live⟩⟩, ?_⟩
  intro i ui bi
  rcases lt_or_eq_of_le ui with lt | rfl
  · exact (bi (L.after i lt)).elim
  · exact L.node_eq_one ha first

private theorem reflectedWeight_tail_of_clock_one {u : Fin s}
    (one : ∀ i, u ≤ i → b i ≠ 0 → nodes A i = 1)
    (k : ℕ) :
    reflectedStageWeight A b (k+1) ∈ tailZero u := by
  apply mem_tailZero.mpr
  intro i ui
  by_cases bi : b i = 0
  · simp [reflectedStageWeight, bi]
  · have yi : reflectedClock A i = 0 := by
      change (1 : K) - nodes A i = 0
      rw [one i ui bi, sub_self]
    simp [reflectedStageWeight, yi, pow_succ]

private theorem reflectedRow_tail_of_clock_one {u : Fin s}
    (ha : ∀ i r, i ≤ r → A i r = 0) (first : firstSeed A b = 0)
    (one : ∀ i, u ≤ i → b i ≠ 0 → nodes A i = 1)
    (k : ℕ) :
    reflectedStageRow A b k ∈ tailZero u := by
  cases k with
  | zero =>
    change firstSeed A b ∈ tailZero u
    rw [first]
    exact (tailZero u).zero_mem
  | succ k =>
    have w := reflectedWeight_tail_of_clock_one one k
    have wz := reflectedWeight_tail_of_clock_one one (k+1)
    apply mem_tailZero.mpr
    intro i ui
    have m : (A.transpose *ᵥ reflectedStageWeight A b (k+1)) i = 0 :=
      transpose_tail_zero ha (t := u) (v := reflectedStageWeight A b (k+1))
        (fun r ur => mem_tailZero.mp w r ur.le) (i := i) ui
    have e : reflectedStageWeight A b (k+1+1) i = 0 :=
      mem_tailZero.mp wz i ui
    change reflectedStageRow A b (k+1) i = 0
    simp only [reflectedStageRow, Pi.sub_apply, Pi.smul_apply, m, e, smul_zero, sub_zero]

/-- The actual all-monomial reverse flag has no support on this physical
suffix. This support fact needs no order payment or positivity. -/
theorem primitiveBack_tail_of_live_clock_one {u : Fin s}
    (ha : ∀ i r, i ≤ r → A i r = 0) (first : firstSeed A b = 0)
    (one : ∀ i, u ≤ i → b i ≠ 0 → nodes A i = 1)
    (n : ℕ) :
    primitiveBack A b n ≤ tailZero u := by
  apply adjointFlag_tail ha first (monomialCredit A b) _ n
  intro l
  apply Submodule.span_le.mpr
  rintro _ ⟨k, rfl⟩
  exact reflectedRow_tail_of_clock_one ha first one k.val

/-- Full saturation on the actual tree space makes every physical suffix
coordinate a literal tree-space member, including zero-output rows. -/
theorem coordinate_mem_treeSpace_of_clock_one_suffix {u i : Fin s} {j n : ℕ}
    (ha : ∀ r t, r ≤ t → A r t = 0) (first : firstSeed A b = 0)
    (one : ∀ r, u ≤ r → b r ≠ 0 → nodes A r = 1)
    (full : primitiveBack A b n = annih (treeSpace A j)) (ui : u ≤ i) :
    coordinate (K := K) i ∈ treeSpace A j := by
  rw [← annih_annih (treeSpace A j)]
  apply mem_annih.mpr
  intro w hw
  have hw' : w ∈ primitiveBack A b n := full.symm ▸ hw
  have hz : w i = 0 :=
    mem_tailZero.mp (primitiveBack_tail_of_live_clock_one ha first one n hw') i ui
  calc
    row (coordinate (K := K) i) w = row w (coordinate (K := K) i) := by
      simp only [row_apply]
      exact dotProduct_comm _ _
    _ = 0 := by rw [row_coordinate, hz]

/-- Inputs for the subsequent paid trace and compensated rank, on exactly
the selected live physical indices. No sign of a weight is strengthened. -/
theorem live_clock_one_suffix_coordinate {u i : Fin s} {j n : ℕ}
    (ha : ∀ r t, r ≤ t → A r t = 0) (first : firstSeed A b = 0)
    (one : ∀ r, u ≤ r → b r ≠ 0 → nodes A r = 1)
    (full : primitiveBack A b n = annih (treeSpace A j))
    (hi : i ∈ suffixLiveStages b u) :
    nodes A i = 1 ∧ b i ≠ 0 ∧ coordinate (K := K) i ∈ treeSpace A j := by
  obtain ⟨ui, bi⟩ := mem_suffixLiveStages.mp hi
  exact ⟨one i ui bi, bi, coordinate_mem_treeSpace_of_clock_one_suffix ha first one full ui⟩

end
end RKResearch.Certified.Graded.Reverse
