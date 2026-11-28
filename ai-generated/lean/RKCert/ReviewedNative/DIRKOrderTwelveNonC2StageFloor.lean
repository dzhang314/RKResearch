module

public import RKCert.ReviewedNative.DIRKTerminalRank

@[expose] public section

/-! The grade-five forward count and one paid terminal refund already
give the width-15 order-twelve floor when the actual quadratic defect
is nonzero; no order thirteen identity or characteristic hypothesis. -/
namespace RKResearch.Certified.Graded.Reverse

open RKResearch Module
open scoped Matrix

variable {K : Type*} [Field K] {s : Nat}
  {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}

theorem dirk_order12_nonC2_floor (ha : A.IsLowerTriangular)
    (ho : HasOrder 12 A b) (h : monomialStageDefect A 1≠0) : 15≤s := by
  have f5 := (dirk_forward_zeroSpace_rank_floor ha ho (q:=5) (by decide) (by decide)).2 h
  have t5 := treeSpace_rank_eq_of_separation ho (q:=5) (by decide)
    (coeff_separated ho (by decide))
  have total := dirk_reverse_room_unanchored ha ho (q:=5) (n:=5)
    (by decide) (by decide) (by decide)
  omega

end RKResearch.Certified.Graded.Reverse

#print axioms RKResearch.Certified.Graded.Reverse.dirk_order12_nonC2_floor
