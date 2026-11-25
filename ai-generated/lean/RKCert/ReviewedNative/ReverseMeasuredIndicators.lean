module

public import RKCert.ReviewedNative.ReverseMeasuredCapacity
public import RKCert.ReviewedNative.EndpointAdjoint

public section

namespace RKResearch.Certified.Graded.Reverse

open RKResearch Module
open scoped BigOperators Matrix

variable {K : Type*} [Field K] {s j n : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}

/-- Enough actual reverse rows make their vanishing an exact column test. -/
theorem MeasuredReverseCapacity.mem_treeSpace_iff_annih_of_full_rank
    (H : MeasuredReverseCapacity A b j n)
    {U : Submodule K (Fin s → K)} (inc : U ≤ back A b n)
    (cover : finrank K (back A b 0) + n ≤ finrank K U) {v : Fin s → K} :
    v ∈ treeSpace A j ↔ v ∈ annih U := by
  have topRank := (H.flagExact n le_rfl).2.1
  have hU : U = back A b n :=
    Submodule.eq_of_le_of_finrank_le inc (by rw [topRank]; exact cover)
  rw [hU, H.backFull, annih_annih]

private theorem span_firstSeed_le_back (k : ℕ) :
    (K ∙ firstSeed A b) ≤ back A b k := by
  change back A b 0 ≤ back A b k
  have mono : Monotone (back A b) :=
    monotone_nat_of_le_succ
      (fun m => adjointFlag_le_succ (A := A) (b := b) (pairCredit A b) m)
  exact mono (Nat.zero_le k)

private theorem mem_annih_adjoin_iff (U : Submodule K (Fin s → K))
    (d v : Fin s → K) :
    v ∈ annih (U ⊔ K ∙ d) ↔ v ∈ annih U ∧ row v d = 0 := by
  constructor
  · intro hv
    have inc : (K ∙ d) ≤ U ⊔ K ∙ d := le_sup_right
    exact ⟨annih_antitone le_sup_left hv,
      mem_annih.mp hv d (inc (Submodule.mem_span_singleton_self d))⟩
  · rintro ⟨hv, hd⟩
    apply mem_annih.mpr
    intro w hw
    obtain ⟨u, hu, z, hz, rfl⟩ := Submodule.mem_sup.mp hw
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
    rw [map_add, map_smul, mem_annih.mp hv u hu, hd, smul_zero, add_zero]

/-- The actual first seed must be included in the tested reverse rank. -/
theorem MeasuredReverseCapacity.mem_treeSpace_iff_of_adjoin_first
    (H : MeasuredReverseCapacity A b j n)
    {U : Submodule K (Fin s → K)} (inc : U ≤ back A b n)
    (cover : finrank K (back A b 0) + n ≤ finrank K (U ⊔ K ∙ firstSeed A b : Submodule K (Fin s → K)))
    {v : Fin s → K} :
    v ∈ treeSpace A j ↔ v ∈ annih U ∧ row v (firstSeed A b) = 0 := by
  have joined : U ⊔ K ∙ firstSeed A b ≤ back A b n :=
    sup_le inc (span_firstSeed_le_back (A := A) (b := b) n)
  exact (H.mem_treeSpace_iff_annih_of_full_rank joined cover (v := v)).trans
    (mem_annih_adjoin_iff U (firstSeed A b) v)

theorem MeasuredReverseCapacity.mem_treeSpace_iff_of_zero_first
    (H : MeasuredReverseCapacity A b j n) (hz : firstSeed A b = 0)
    {U : Submodule K (Fin s → K)} (inc : U ≤ back A b n)
    (enough : n ≤ finrank K U) {v : Fin s → K} :
    v ∈ treeSpace A j ↔ v ∈ annih U := by
  apply H.mem_treeSpace_iff_annih_of_full_rank inc
  rw [first_dim_zero hz, zero_add]
  exact enough

/-- A transverse first seed adds one direction, with its own balance test. -/
theorem MeasuredReverseCapacity.mem_treeSpace_iff_of_first_transverse
    (H : MeasuredReverseCapacity A b j n)
    {U : Submodule K (Fin s → K)} (inc : U ≤ back A b n)
    (enough : n ≤ finrank K U) (transverse : firstSeed A b ∉ U)
    {v : Fin s → K} :
    v ∈ treeSpace A j ↔ v ∈ annih U ∧ row v (firstSeed A b) = 0 := by
  have first : firstSeed A b ≠ 0 := by
    intro hz
    apply transverse
    rw [hz]
    exact U.zero_mem
  apply H.mem_treeSpace_iff_of_adjoin_first inc
  rw [first_dim_one first, Submodule.finrank_sup_span_singleton transverse]
  omega

/-- Pairing with the whole physical indicator is the unweighted row sum
on that stage set, including zero or cancelled entries. -/
theorem row_sum_stage_coordinates (S : Finset (Fin s)) (w : Fin s → K) :
    row (∑ i ∈ S, coordinate (K := K) i) w = ∑ i ∈ S, w i := by
  calc
    row (∑ i ∈ S, coordinate (K := K) i) w =
        row w (∑ i ∈ S, coordinate (K := K) i) := by simpa only [row_apply] using dotProduct_comm (∑ i ∈ S, coordinate (K := K) i) w
    _ = _ := by simp only [map_sum, row_coordinate]

end RKResearch.Certified.Graded.Reverse
