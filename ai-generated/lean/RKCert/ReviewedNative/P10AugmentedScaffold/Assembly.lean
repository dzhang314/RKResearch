module

public import RKCert.ReviewedNative.P10AugmentedScaffold.Vectors
public import RKCert.ReviewedNative.P10AugmentedScaffold.LowerG02
public import RKCert.ReviewedNative.P10AugmentedScaffold.LowerG03
public import RKCert.ReviewedNative.P10AugmentedScaffold.LowerG04
public import RKCert.ReviewedNative.P10AugmentedScaffold.LowerG05
public import RKCert.ReviewedNative.P10AugmentedScaffold.LowerG06
public import RKCert.ReviewedNative.P10AugmentedScaffold.LowerG07
public import RKCert.ReviewedNative.P10AugmentedScaffold.LowerG08
public import RKCert.ReviewedNative.P10AugmentedScaffold.LowerG09
public import RKCert.ReviewedNative.P10AugmentedScaffold.Top10

@[expose] public section

namespace RKResearch.Certified.P10AugmentedScaffold

open NativeIntegerSpanClearing NativeIntegerAugmentedChecker NativeIntegerAugmentedShardJoin
open NativeIntegerAugmentedTopPay RootedTreeAugmentedSpan
open scoped Matrix

/-- All structural shard contracts, without a supplied value of one or any
new axiom. There is no 'prove an arbitrary omitted key' fallback. -/
structure Receipts (O : Ops) (H : Header) (L : LowerPayload) : Prop where
  scales : checkScales O.d O.e = true
  leaf : checkLeaf (base H) = true
  vectors : VectorReceipts O H
  g02 : LowerG02Receipts O H L
  g03 : LowerG03Receipts O H L
  g04 : LowerG04Receipts O H L
  g05 : LowerG05Receipts O H L
  g06 : LowerG06Receipts O H L
  g07 : LowerG07Receipts O H L
  g08 : LowerG08Receipts O H L
  g09 : LowerG09Receipts O H L
  top : Top10Receipts O H

theorem Receipts.members_get (O : Ops) (H : Header) (L : LowerPayload) (R : Receipts O H L)
    (k l : ℕ) (hk : 0 < k) (hl : 0 < l) (hp : k+l ≤ 9)
    (i : Fin (rank k)) (j : Fin (rank l)) :
    checkProduct O.d (candidate H L) k l i j = true := by
  have hsums : k + l = 2 ∨ k + l = 3 ∨ k + l = 4 ∨ k + l = 5 ∨ k + l = 6 ∨ k + l = 7 ∨ k + l = 8 ∨ k + l = 9 := by omega
  rcases hsums with hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase
  · exact LowerG02Receipts.get O H L R.g02 k l hk hl hcase i j
  · exact LowerG03Receipts.get O H L R.g03 k l hk hl hcase i j
  · exact LowerG04Receipts.get O H L R.g04 k l hk hl hcase i j
  · exact LowerG05Receipts.get O H L R.g05 k l hk hl hcase i j
  · exact LowerG06Receipts.get O H L R.g06 k l hk hl hcase i j
  · exact LowerG07Receipts.get O H L R.g07 k l hk hl hcase i j
  · exact LowerG08Receipts.get O H L R.g08 k l hk hl hcase i j
  · exact LowerG09Receipts.get O H L R.g09 k l hk hl hcase i j

theorem points (O : Ops) (H : Header) (L : LowerPayload) (R : Receipts O H L) :
    DirectTopPoints O.act O.out O.d O.e 10 (candidate H L) := by
  refine ⟨by decide, R.scales, R.leaf, ?_, ?_, ?_, ?_⟩
  · intro l hl hb j
    exact VectorReceipts.actions_get O H L R.vectors l hl hb j
  · intro k l hk hl hb i j
    exact Receipts.members_get O H L R k l hk hl hb i j
  · intro n hn hb i
    exact VectorReceipts.payments_get O H L R.vectors n hn hb i
  · intro k l hk hl hb i j
    exact Top10Receipts.get O H L R.top k l hk hl hb i j

theorem assembled_check (O : Ops) (H : Header) (L : LowerPayload) (R : Receipts O H L) :
    checkDirectTop O.act O.out O.d O.e 10 (candidate H L) = true :=
  checkDirectTop_of_points (points O H L R)

/-- The terminal proof targets the true residual's kernel. A final basis
or a dimension computation is not an assumption. Only actions and top
scalar shards are used by this lemma. -/
theorem terminalPair_mem_paidKernel
    (A : Matrix (Fin 27) (Fin 27) ℤ) (b : ZVec 27) (O : Ops)
    (hact : ∀ v, O.act v = A *ᵥ v) (hout : ∀ v, O.out v = b ⬝ᵥ v)
    (H : Header) (L : LowerPayload) (V : VectorReceipts O H) (T : Top10Receipts O H)
    (k l : ℕ) (hk : 0 < k) (hl : 0 < l) (hs : k+l = 10)
    (i : Fin (rank k)) (j : Fin (rank l)) :
    attachBilin (ratMatrix A) (O.d : ℚ) l (ratFeature (H.rows k i)) (ratFeature (H.rows l j)) ∈
      (residual (ratVec b) (O.e : ℚ) 10).ker := by
  have ha : checkActions O.act 10 (candidate H L) = true :=
    actions_of_points (VectorReceipts.actions_get O H L V)
  have ht : checkTopPayments O.out O.d O.e 10 (candidate H L) = true :=
    top_of_points (Top10Receipts.get O H L T)
  have hs' := checkTopPayments_sound A b O.act O.out hact hout O.d O.e
    (candidate H L) ha ht k l hk hl hs
    (ratFeature (H.rows k i)) ⟨i, rfl⟩ (ratFeature (H.rows l j)) ⟨j, rfl⟩
  exact LinearMap.mem_ker.mpr hs'

end RKResearch.Certified.P10AugmentedScaffold
