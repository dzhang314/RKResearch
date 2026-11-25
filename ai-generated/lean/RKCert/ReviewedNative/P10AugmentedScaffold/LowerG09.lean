module

public import RKCert.ReviewedNative.P10AugmentedScaffold.Shape

@[expose] public section

namespace RKResearch.Certified.P10AugmentedScaffold

open NativeIntegerAugmentedChecker

structure LowerG09Receipts (O : Ops) (H : Header) (L : LowerPayload) : Prop where
  split01_08 : LowerSplitWindows O H L 1 8 (by decide) (by decide) (by decide)
  split02_07 : LowerSplitWindows O H L 2 7 (by decide) (by decide) (by decide)
  split03_06 : LowerSplitWindows O H L 3 6 (by decide) (by decide) (by decide)
  split04_05 : LowerSplitWindows O H L 4 5 (by decide) (by decide) (by decide)
  split05_04 : LowerSplitWindows O H L 5 4 (by decide) (by decide) (by decide)
  split06_03 : LowerSplitWindows O H L 6 3 (by decide) (by decide) (by decide)
  split07_02 : LowerSplitWindows O H L 7 2 (by decide) (by decide) (by decide)
  split08_01 : LowerSplitWindows O H L 8 1 (by decide) (by decide) (by decide)

theorem LowerG09Receipts.get (O : Ops) (H : Header) (L : LowerPayload)
    (R : LowerG09Receipts O H L) (k l : ℕ) (hk : 0 < k) (hl : 0 < l) (hs : k+l = 9)
    (i : Fin (rank k)) (j : Fin (rank l)) :
    checkProduct O.d (candidate H L) k l i j = true := by
  have hcases : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 := by omega
  rcases hcases with hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase
  · subst k
    have he : l = 8 := by omega
    subst l
    exact LowerSplitWindows.get O H L 1 8 (by decide) (by decide) (by decide) R.split01_08 i j
  · subst k
    have he : l = 7 := by omega
    subst l
    exact LowerSplitWindows.get O H L 2 7 (by decide) (by decide) (by decide) R.split02_07 i j
  · subst k
    have he : l = 6 := by omega
    subst l
    exact LowerSplitWindows.get O H L 3 6 (by decide) (by decide) (by decide) R.split03_06 i j
  · subst k
    have he : l = 5 := by omega
    subst l
    exact LowerSplitWindows.get O H L 4 5 (by decide) (by decide) (by decide) R.split04_05 i j
  · subst k
    have he : l = 4 := by omega
    subst l
    exact LowerSplitWindows.get O H L 5 4 (by decide) (by decide) (by decide) R.split05_04 i j
  · subst k
    have he : l = 3 := by omega
    subst l
    exact LowerSplitWindows.get O H L 6 3 (by decide) (by decide) (by decide) R.split06_03 i j
  · subst k
    have he : l = 2 := by omega
    subst l
    exact LowerSplitWindows.get O H L 7 2 (by decide) (by decide) (by decide) R.split07_02 i j
  · subst k
    have he : l = 1 := by omega
    subst l
    exact LowerSplitWindows.get O H L 8 1 (by decide) (by decide) (by decide) R.split08_01 i j

end RKResearch.Certified.P10AugmentedScaffold
