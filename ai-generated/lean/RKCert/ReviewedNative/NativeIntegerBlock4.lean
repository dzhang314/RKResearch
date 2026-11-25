module

public import RKCert.ReviewedNative.NativeIntegerAugmentedShardJoin

@[expose] public section

/-! Width-four partitions of actual finite indices. No tableau or numerical receipt. -/
namespace RKResearch.Certified.NativeIntegerBlock4

open NativeIntegerSpanClearing NativeIntegerAugmentedShardJoin

def count (r : ℕ) : ℕ := (r + 3) / 4

abbrev Block (r : ℕ) := Fin (count r)

def lo {r : ℕ} (b : Block r) : ℕ := 4 * b.val

def hi {r : ℕ} (b : Block r) : ℕ := min (lo b + 4) r

def len {r : ℕ} (b : Block r) : ℕ := hi b - lo b

theorem lo_lt_rank {r : ℕ} (b : Block r) : lo b < r := by
  have hb : b.val < (r + 3) / 4 := b.isLt
  change 4 * b.val < r
  omega

theorem hi_le_rank {r : ℕ} (b : Block r) : hi b ≤ r :=
  Nat.min_le_right _ _

theorem hi_le_lo_add_four {r : ℕ} (b : Block r) : hi b ≤ lo b + 4 :=
  Nat.min_le_left _ _

theorem lo_lt_hi {r : ℕ} (b : Block r) : lo b < hi b := by
  change lo b < min (lo b + 4) r
  exact Nat.lt_min.mpr ⟨by omega, lo_lt_rank b⟩

theorem lo_add_len {r : ℕ} (b : Block r) : lo b + len b = hi b := by
  have h := lo_lt_hi b
  change lo b + (hi b - lo b) = hi b
  omega

theorem blockBound {r : ℕ} (b : Block r) : lo b + len b ≤ r := by
  rw [lo_add_len]
  exact hi_le_rank b

theorem len_le_four {r : ℕ} (b : Block r) : len b ≤ 4 := by
  have h := hi_le_lo_add_four b
  change hi b - lo b ≤ 4
  omega

def index {r : ℕ} (b : Block r) (t : Fin (len b)) : Fin r :=
  blockIndex (lo b) (len b) (blockBound b) t

theorem index_lo {r : ℕ} (b : Block r) (t : Fin (len b)) :
    lo b ≤ (index b t).val := by
  change lo b ≤ lo b + t.val
  omega

theorem index_hi {r : ℕ} (b : Block r) (t : Fin (len b)) :
    (index b t).val < hi b := by
  have ht := t.isLt
  have hb := lo_add_len b
  change lo b + t.val < hi b
  omega

def atIndex {r : ℕ} (j : Fin r) : Block r :=
  ⟨j.val / 4, by
    have hj := j.isLt
    change j.val / 4 < (r + 3) / 4
    omega⟩

theorem at_lo {r : ℕ} (j : Fin r) : lo (atIndex j) ≤ j.val := by
  change 4 * (j.val / 4) ≤ j.val
  omega

theorem at_hi {r : ℕ} (j : Fin r) : j.val < hi (atIndex j) := by
  change j.val < min (4 * (j.val / 4) + 4) r
  exact Nat.lt_min.mpr ⟨by omega, j.isLt⟩

/-- The typed, half-open window containing an actual index is unique. -/
theorem at_eq_of_bounds {r : ℕ} (b : Block r) (j : Fin r)
    (hlo : lo b ≤ j.val) (hhi : j.val < hi b) : atIndex j = b := by
  have htop := hi_le_lo_add_four b
  have hlarge : j.val < lo b + 4 := lt_of_lt_of_le hhi htop
  change 4 * b.val ≤ j.val at hlo
  change j.val < 4 * b.val + 4 at hlarge
  apply Fin.ext
  change j.val / 4 = b.val
  omega

def offset {r : ℕ} (b : Block r) (j : Fin r)
    (hlo : lo b ≤ j.val) (hhi : j.val < hi b) : Fin (len b) :=
  ⟨j.val - lo b, by
    change j.val - lo b < hi b - lo b
    omega⟩

theorem index_offset {r : ℕ} (b : Block r) (j : Fin r)
    (hlo : lo b ≤ j.val) (hhi : j.val < hi b) :
    index b (offset b j hlo hhi) = j := by
  apply Fin.ext
  change lo b + (j.val - lo b) = j.val
  omega

def checkWindow {r : ℕ} (test : Fin r → Bool) (b : Block r) : Bool :=
  checkIndices (fun t => test (index b t))

def AllWindows {r : ℕ} (test : Fin r → Bool) : Prop :=
  ∀ b : Block r, checkWindow test b = true

theorem AllWindows.get {r : ℕ} {test : Fin r → Bool} (h : AllWindows test)
    (j : Fin r) : test j = true := by
  let b : Block r := atIndex j
  let t : Fin (len b) := offset b j (at_lo j) (at_hi j)
  have hwin : checkIndices (fun q => test (index b q)) = true := h b
  have hj : index b t = j := index_offset b j _ _
  rw [← hj]
  exact checkIndices_get hwin t

end RKResearch.Certified.NativeIntegerBlock4
