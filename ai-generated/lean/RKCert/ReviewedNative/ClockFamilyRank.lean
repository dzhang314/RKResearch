module
public import RKCert.ReviewedNative.ClockLocalFiberRank
public import RKCert.ReviewedNative.PaidClockLocalRank
public import Mathlib.Data.Finset.Lattice.Fold

@[expose] public section

/-! # Independent charges combine by spanning actual images at each clock -/
namespace RKResearch.Certified.Graded.Reverse

open Module
open scoped BigOperators Classical

noncomputable section

variable {K α : Type*} [Field K] {s : ℕ}

/-- The actual span of the selected family images in one original clock fibre. -/
def clockFamilyFiber (c : Fin s → K) (Q : α → Submodule K (Fin s → K))
    (F : Finset α) (x : ClockSite c) : Submodule K (ClockFiber c x → K) :=
  F.sup (fun a => clockFiberColumns c (Q a) x)

/-- The fibre rank of the same family, counting a local direction only once. -/
def clockFamilyRank (c : Fin s → K) (Q : α → Submodule K (Fin s → K))
    (F : Finset α) : ℕ :=
  ∑ x : ClockSite c, finrank K (clockFamilyFiber c Q F x)

/-- The new ranks after subtracting the *actual* overlaps in each fibre. -/
def clockFamilyGain (c : Fin s → K) (Q : α → Submodule K (Fin s → K))
    (F : Finset α) (a : α) : ℕ :=
  ∑ x : ClockSite c, (finrank K (clockFiberColumns c (Q a) x) -
    finrank K ↥(clockFiberColumns c (Q a) x ⊓ clockFamilyFiber c Q F x :
      Submodule K (ClockFiber c x → K)))

theorem clockFamilyFiber_eq_columns_sup (c : Fin s → K)
    (Q : α → Submodule K (Fin s → K)) (F : Finset α) (x : ClockSite c) :
    clockFamilyFiber c Q F x = clockFiberColumns c (F.sup Q) x := by
  simp only [clockFamilyFiber, clockFiberColumns, Finset.sup_eq_iSup, Submodule.map_iSup]

@[simp] theorem clockFamilyRank_empty (c : Fin s → K)
    (Q : α → Submodule K (Fin s → K)) : clockFamilyRank c Q ∅ = 0 := by
  unfold clockFamilyRank
  refine Finset.sum_eq_zero (fun x _ => ?_)
  have empty : clockFamilyFiber c Q (∅ : Finset α) x = ⊥ := by
    apply le_antisymm
    · unfold clockFamilyFiber
      exact Finset.sup_le (fun a ha => (Finset.notMem_empty a ha).elim)
    · exact bot_le
  exact Submodule.finrank_eq_zero.mpr empty

theorem clockFamilyFiber_mono (c : Fin s → K) (Q : α → Submodule K (Fin s → K))
    {F G : Finset α} (h : F ⊆ G) (x : ClockSite c) :
    clockFamilyFiber c Q F x ≤ clockFamilyFiber c Q G x := by
  unfold clockFamilyFiber
  exact Finset.sup_mono h

theorem clockFamilyRank_mono (c : Fin s → K) (Q : α → Submodule K (Fin s → K))
    {F G : Finset α} (h : F ⊆ G) : clockFamilyRank c Q F ≤ clockFamilyRank c Q G := by
  unfold clockFamilyRank
  exact Finset.sum_le_sum (fun x _ => Submodule.finrank_mono (clockFamilyFiber_mono c Q h x))

/-- Correct addition even when the new member overlaps the family in several fibres. -/
theorem clockFamilyRank_insert (c : Fin s → K) (Q : α → Submodule K (Fin s → K))
    (F : Finset α) (a : α) :
    clockFamilyRank c Q (insert a F) = clockFamilyRank c Q F + clockFamilyGain c Q F a := by
  unfold clockFamilyRank clockFamilyGain
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  let L := clockFiberColumns c (Q a) x
  let R := clockFamilyFiber c Q F x
  have step : clockFamilyFiber c Q (insert a F) x = L ⊔ R := by
    simp only [L, R, clockFamilyFiber, Finset.sup_insert]
  rw [step]
  change finrank K ↥(L ⊔ R : Submodule K (ClockFiber c x → K)) =
    finrank K R + (finrank K L - finrank K ↥(L ⊓ R : Submodule K (ClockFiber c x → K)))
  have dim := Submodule.finrank_sup_add_finrank_inf_eq L R
  have overlap := Submodule.finrank_mono (inf_le_left : L ⊓ R ≤ L)
  omega

/-- Diminishing returns on the family of subspaces, not on their supports. -/
theorem clockFamilyGain_antitone (c : Fin s → K) (Q : α → Submodule K (Fin s → K))
    {F G : Finset α} (h : F ⊆ G) (a : α) : clockFamilyGain c Q G a ≤ clockFamilyGain c Q F a := by
  unfold clockFamilyGain
  refine Finset.sum_le_sum (fun x _ => ?_)
  let L := clockFiberColumns c (Q a) x
  have inc : L ⊓ clockFamilyFiber c Q F x ≤ L ⊓ clockFamilyFiber c Q G x :=
    inf_le_inf le_rfl (clockFamilyFiber_mono c Q h x)
  exact Nat.sub_le_sub_left (Submodule.finrank_mono inc) _

/-- Combining independently admitted spaces inside a clock-stable container
requires only their individual inclusions. -/
theorem clockFamilyRank_le_stable (c : Fin s → K) (Q : α → Submodule K (Fin s → K))
    (F : Finset α) {W : Submodule K (Fin s → K)} (stable : W.map (diag c) ≤ W)
    (inside : ∀ a ∈ F, Q a ≤ W) : clockFamilyRank c Q F ≤ finrank K W := by
  have sAnn : (annih W).map (diag c) ≤ annih W :=
    annih_map_diag (Submodule.map_le_iff_le_comap.mp stable)
  have total := finrank_clockLocal_annih_add_sum_eq c W
  rw [(clockLocal_eq_iff c (annih W)).mpr sAnn] at total
  have codim := finrank_annih W
  rw [Fintype.card_fin] at codim
  have dim : (∑ x : ClockSite c, finrank K (clockFiberColumns c W x)) = finrank K W := by omega
  rw [← dim]
  unfold clockFamilyRank
  refine Finset.sum_le_sum (fun x _ => Submodule.finrank_mono ?_)
  change F.sup (fun a => (Q a).map (clockFiberRestrict c x)) ≤ W.map (clockFiberRestrict c x)
  exact Finset.sup_le (fun a ha => Submodule.map_mono (inside a ha))

variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K} {j n : ℕ}

/-- The actual staircase caps a whole family from separate local certificates.
There is no premise about any union of their supports. -/
theorem clockFamilyRank_le_of_staircase (H : PaidClockCapacityStaircase A b j n)
    (positive : 1 ≤ n) (Q : α → Submodule K (Fin s → K)) (F : Finset α)
    (inside : ∀ a ∈ F, Q a ≤ clockLocal (nodes A) (annih (treeSpace A j))) :
    clockFamilyRank (nodes A) Q F ≤ finrank K (back A b 0) + 1 :=
  (clockFamilyRank_le_stable (nodes A) Q F (clockLocal_stable (nodes A) (annih (treeSpace A j)))
    inside).trans (paid_clock_local_rank_of_staircase H positive).rankCap

end
end RKResearch.Certified.Graded.Reverse
