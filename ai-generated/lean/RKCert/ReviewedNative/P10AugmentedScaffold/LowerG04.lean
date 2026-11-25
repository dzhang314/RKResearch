module

public import RKCert.ReviewedNative.P10AugmentedScaffold.Shape

@[expose] public section

namespace RKResearch.Certified.P10AugmentedScaffold

open NativeIntegerAugmentedChecker

structure LowerG04Receipts (O : Ops) (H : Header) (L : LowerPayload) : Prop where
  split01_03 : LowerSplitWindows O H L 1 3 (by decide) (by decide) (by decide)
  split02_02 : LowerSplitWindows O H L 2 2 (by decide) (by decide) (by decide)
  split03_01 : LowerSplitWindows O H L 3 1 (by decide) (by decide) (by decide)

theorem LowerG04Receipts.get (O : Ops) (H : Header) (L : LowerPayload)
    (R : LowerG04Receipts O H L) (k l : ℕ) (hk : 0 < k) (hl : 0 < l) (hs : k+l = 4)
    (i : Fin (rank k)) (j : Fin (rank l)) :
    checkProduct O.d (candidate H L) k l i j = true := by
  have hcases : k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hcases with hcase | hcase | hcase
  · subst k
    have he : l = 3 := by omega
    subst l
    exact LowerSplitWindows.get O H L 1 3 (by decide) (by decide) (by decide) R.split01_03 i j
  · subst k
    have he : l = 2 := by omega
    subst l
    exact LowerSplitWindows.get O H L 2 2 (by decide) (by decide) (by decide) R.split02_02 i j
  · subst k
    have he : l = 1 := by omega
    subst l
    exact LowerSplitWindows.get O H L 3 1 (by decide) (by decide) (by decide) R.split03_01 i j

end RKResearch.Certified.P10AugmentedScaffold
