module
public import RKCert.ReviewedNative.ClockLocalFiberRank

@[expose] public section

/-! # Nonzero original clock fibres of a clock-stable space -/
namespace RKResearch.Certified.Graded.Reverse

open Module RKCert.Endpoint
open scoped BigOperators Classical

noncomputable section

variable {K : Type*} [Field K] {s : ℕ}

/-- The original clock sites on which the space has a nonzero restricted column. -/
def clockFiberSupport (c : Fin s → K) (W : Submodule K (Fin s → K)) : Finset (ClockSite c) :=
  Finset.univ.filter (fun x => clockFiberColumns c W x ≠ ⊥)

@[simp] theorem mem_clockFiberSupport {c : Fin s → K} {W : Submodule K (Fin s → K)}
    {x : ClockSite c} : x ∈ clockFiberSupport c W ↔ clockFiberColumns c W x ≠ ⊥ := by
  simp only [clockFiberSupport, Finset.mem_filter, Finset.mem_univ, true_and]

/-- A clock-stable space has no rank loss or overlap between its physical fibre ranks. -/
theorem sum_finrank_clockFiberColumns_eq_of_stable
    (c : Fin s → K) (W : Submodule K (Fin s → K)) (stable : W.map (diag c) ≤ W) :
    (∑ x : ClockSite c, finrank K (clockFiberColumns c W x)) = finrank K W := by
  have stableAnn : (annih W).map (diag c) ≤ annih W :=
    annih_map_diag (Submodule.map_le_iff_le_comap.mp stable)
  have localRank := finrank_clockLocal_annih_add_sum_eq c W
  rw [(clockLocal_eq_iff c (annih W)).mpr stableAnn] at localRank
  have wholeRank := finrank_annih W
  rw [Fintype.card_fin] at wholeRank
  omega

/-- In a clock-stable space each nonzero original fibre costs at least one dimension. -/
theorem clockFiberSupport_card_le_finrank_of_stable
    (c : Fin s → K) (W : Submodule K (Fin s → K)) (stable : W.map (diag c) ≤ W) :
    (clockFiberSupport c W).card ≤ finrank K W := by
  rw [clockFiberSupport, Finset.card_eq_sum_ones, Finset.sum_filter,
    ← sum_finrank_clockFiberColumns_eq_of_stable c W stable]
  refine Finset.sum_le_sum (fun x _ => ?_)
  split
  · exact Submodule.one_le_finrank_iff.mpr (by assumption)
  · exact Nat.zero_le _

/-- The low-dimensional clock-stable cap is a cap on the actual nonzero fibres. -/
theorem clockFiberSupport_card_le_two_of_stable
    (c : Fin s → K) (W : Submodule K (Fin s → K)) (stable : W.map (diag c) ≤ W)
    (dimW : finrank K W ≤ 2) : (clockFiberSupport c W).card ≤ 2 :=
  (clockFiberSupport_card_le_finrank_of_stable c W stable).trans dimW

end
end RKResearch.Certified.Graded.Reverse
