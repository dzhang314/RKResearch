module

public import RKCert.ReviewedNative.P10AugmentedScaffold.Shape

@[expose] public section

namespace RKResearch.Certified.P10AugmentedScaffold

open NativeIntegerAugmentedChecker

structure Top10Receipts (O : Ops) (H : Header) : Prop where
  split01_09 : TopSplitWindows O H 1 9
  split02_08 : TopSplitWindows O H 2 8
  split03_07 : TopSplitWindows O H 3 7
  split04_06 : TopSplitWindows O H 4 6
  split05_05 : TopSplitWindows O H 5 5
  split06_04 : TopSplitWindows O H 6 4
  split07_03 : TopSplitWindows O H 7 3
  split08_02 : TopSplitWindows O H 8 2
  split09_01 : TopSplitWindows O H 9 1

theorem Top10Receipts.get (O : Ops) (H : Header) (L : LowerPayload)
    (R : Top10Receipts O H) (k l : ℕ) (hk : 0 < k) (hl : 0 < l) (hs : k+l = 10)
    (i : Fin (rank k)) (j : Fin (rank l)) :
    checkPayment O.out O.e 10 (joinedZ O.d (candidate H L) k l i j) = true := by
  have hcases : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 := by omega
  rcases hcases with hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase
  · subst k
    have he : l = 9 := by omega
    subst l
    exact TopSplitWindows.get O H L 1 9 R.split01_09 i j
  · subst k
    have he : l = 8 := by omega
    subst l
    exact TopSplitWindows.get O H L 2 8 R.split02_08 i j
  · subst k
    have he : l = 7 := by omega
    subst l
    exact TopSplitWindows.get O H L 3 7 R.split03_07 i j
  · subst k
    have he : l = 6 := by omega
    subst l
    exact TopSplitWindows.get O H L 4 6 R.split04_06 i j
  · subst k
    have he : l = 5 := by omega
    subst l
    exact TopSplitWindows.get O H L 5 5 R.split05_05 i j
  · subst k
    have he : l = 4 := by omega
    subst l
    exact TopSplitWindows.get O H L 6 4 R.split06_04 i j
  · subst k
    have he : l = 3 := by omega
    subst l
    exact TopSplitWindows.get O H L 7 3 R.split07_03 i j
  · subst k
    have he : l = 2 := by omega
    subst l
    exact TopSplitWindows.get O H L 8 2 R.split08_02 i j
  · subst k
    have he : l = 1 := by omega
    subst l
    exact TopSplitWindows.get O H L 9 1 R.split09_01 i j

end RKResearch.Certified.P10AugmentedScaffold
