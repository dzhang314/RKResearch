module

public import RKCert.ReviewedNative.P10AugmentedScaffold.Shape

@[expose] public section

namespace RKResearch.Certified.P10AugmentedScaffold

open NativeIntegerAugmentedChecker

structure LowerG02Receipts (O : Ops) (H : Header) (L : LowerPayload) : Prop where
  split01_01 : LowerSplitWindows O H L 1 1 (by decide) (by decide) (by decide)

theorem LowerG02Receipts.get (O : Ops) (H : Header) (L : LowerPayload)
    (R : LowerG02Receipts O H L) (k l : ℕ) (hk : 0 < k) (hl : 0 < l) (hs : k+l = 2)
    (i : Fin (rank k)) (j : Fin (rank l)) :
    checkProduct O.d (candidate H L) k l i j = true := by
  have hcases : k = 1 := by omega
  subst k
  have he : l = 1 := by omega
  subst l
  exact LowerSplitWindows.get O H L 1 1 (by decide) (by decide) (by decide) R.split01_01 i j

end RKResearch.Certified.P10AugmentedScaffold
