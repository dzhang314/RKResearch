module

public import RKCert.ReviewedNative.P10AugmentedScaffold.Shape

@[expose] public section

namespace RKResearch.Certified.P10AugmentedScaffold

open NativeIntegerAugmentedChecker

structure VectorReceipts (O : Ops) (H : Header) : Prop where
  action01 : ActionWindows O H 1
  payment01 : PayWindows O H 1
  action02 : ActionWindows O H 2
  payment02 : PayWindows O H 2
  action03 : ActionWindows O H 3
  payment03 : PayWindows O H 3
  action04 : ActionWindows O H 4
  payment04 : PayWindows O H 4
  action05 : ActionWindows O H 5
  payment05 : PayWindows O H 5
  action06 : ActionWindows O H 6
  payment06 : PayWindows O H 6
  action07 : ActionWindows O H 7
  payment07 : PayWindows O H 7
  action08 : ActionWindows O H 8
  payment08 : PayWindows O H 8
  action09 : ActionWindows O H 9
  payment09 : PayWindows O H 9

theorem VectorReceipts.actions_get (O : Ops) (H : Header) (L : LowerPayload)
    (R : VectorReceipts O H) (n : ℕ) (hn : 0 < n) (hp : n < 10)
    (i : Fin (rank n)) : checkAction O.act (candidate H L) n i = true := by
  have hcases : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 := by omega
  rcases hcases with hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase
  · subst n
    exact ActionWindows.get O H L 1 R.action01 i
  · subst n
    exact ActionWindows.get O H L 2 R.action02 i
  · subst n
    exact ActionWindows.get O H L 3 R.action03 i
  · subst n
    exact ActionWindows.get O H L 4 R.action04 i
  · subst n
    exact ActionWindows.get O H L 5 R.action05 i
  · subst n
    exact ActionWindows.get O H L 6 R.action06 i
  · subst n
    exact ActionWindows.get O H L 7 R.action07 i
  · subst n
    exact ActionWindows.get O H L 8 R.action08 i
  · subst n
    exact ActionWindows.get O H L 9 R.action09 i

theorem VectorReceipts.payments_get (O : Ops) (H : Header) (L : LowerPayload)
    (R : VectorReceipts O H) (n : ℕ) (hn : 0 < n) (hp : n ≤ 9)
    (i : Fin (rank n)) : checkPayment O.out O.e n ((candidate H L).rows n i) = true := by
  have hcases : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 := by omega
  rcases hcases with hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase
  · subst n
    exact PayWindows.get O H L 1 R.payment01 i
  · subst n
    exact PayWindows.get O H L 2 R.payment02 i
  · subst n
    exact PayWindows.get O H L 3 R.payment03 i
  · subst n
    exact PayWindows.get O H L 4 R.payment04 i
  · subst n
    exact PayWindows.get O H L 5 R.payment05 i
  · subst n
    exact PayWindows.get O H L 6 R.payment06 i
  · subst n
    exact PayWindows.get O H L 7 R.payment07 i
  · subst n
    exact PayWindows.get O H L 8 R.payment08 i
  · subst n
    exact PayWindows.get O H L 9 R.payment09 i

end RKResearch.Certified.P10AugmentedScaffold
