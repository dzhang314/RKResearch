module

public import RKCert.ReviewedNative.P10AugmentedScaffold.Shape

@[expose] public section

namespace RKResearch.Certified.P10AugmentedScaffold

open NativeIntegerAugmentedChecker

structure LowerG06Receipts (O : Ops) (H : Header) (L : LowerPayload) : Prop where
  split01_05 : LowerSplitWindows O H L 1 5 (by decide) (by decide) (by decide)
  split02_04 : LowerSplitWindows O H L 2 4 (by decide) (by decide) (by decide)
  split03_03 : LowerSplitWindows O H L 3 3 (by decide) (by decide) (by decide)
  split04_02 : LowerSplitWindows O H L 4 2 (by decide) (by decide) (by decide)
  split05_01 : LowerSplitWindows O H L 5 1 (by decide) (by decide) (by decide)

theorem LowerG06Receipts.get (O : Ops) (H : Header) (L : LowerPayload)
    (R : LowerG06Receipts O H L) (k l : ℕ) (hk : 0 < k) (hl : 0 < l) (hs : k+l = 6)
    (i : Fin (rank k)) (j : Fin (rank l)) :
    checkProduct O.d (candidate H L) k l i j = true := by
  have hcases : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
  rcases hcases with hcase | hcase | hcase | hcase | hcase
  · subst k
    have he : l = 5 := by omega
    subst l
    exact LowerSplitWindows.get O H L 1 5 (by decide) (by decide) (by decide) R.split01_05 i j
  · subst k
    have he : l = 4 := by omega
    subst l
    exact LowerSplitWindows.get O H L 2 4 (by decide) (by decide) (by decide) R.split02_04 i j
  · subst k
    have he : l = 3 := by omega
    subst l
    exact LowerSplitWindows.get O H L 3 3 (by decide) (by decide) (by decide) R.split03_03 i j
  · subst k
    have he : l = 2 := by omega
    subst l
    exact LowerSplitWindows.get O H L 4 2 (by decide) (by decide) (by decide) R.split04_02 i j
  · subst k
    have he : l = 1 := by omega
    subst l
    exact LowerSplitWindows.get O H L 5 1 (by decide) (by decide) (by decide) R.split05_01 i j

end RKResearch.Certified.P10AugmentedScaffold
