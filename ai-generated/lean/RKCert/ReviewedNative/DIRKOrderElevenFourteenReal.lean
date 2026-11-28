module

public import RKCert.ReviewedNative.DIRK11Width14IntegerReceipts
public import RKCert.ReviewedNative.DIRK11Width14IntegerRoots

@[expose] public section

/-! Exact order eleven for the literal fourteen-stage real DIRK tableau. -/
namespace RKResearch.Certified.DIRKOrderElevenFourteenReal

open RKResearch QuadTowerIntReplay
open DIRK11Width14IntegerCore DIRK11Width14IntegerData DIRK11Width14IntegerChecks

/-- Any characteristic-zero field containing these four indicated roots
has this same exact order-eleven DIRK witness. -/
theorem exact_of_roots {K : Type*} [Field K] [CharZero K] {x y z w : K}
    (h : Roots reductions x y z w) :
    (A packet x y z w).IsLowerTriangular ∧
    HasOrder 11 (A packet x y z w) (b packet x y z w) ∧
    ¬ HasOrder 12 (A packet x y z w) (b packet x y z w) :=
  ⟨lower packet x y z w,order_eleven h receipts,no_order_twelve h receipts⟩

/-- This assertion concerns existence, not minimality at fourteen stages. -/
theorem exists_exact_real :
    ∃ (A : Matrix (Fin 14) (Fin 14) ℝ) (b : Fin 14 → ℝ),
      A.IsLowerTriangular ∧ HasOrder 11 A b ∧ ¬ HasOrder 12 A b := by
  obtain ⟨x,y,z,w,_,_,_,_,h⟩ := positive_real_roots
  exact ⟨A packet x y z w,b packet x y z w,exact_of_roots h⟩

end RKResearch.Certified.DIRKOrderElevenFourteenReal
