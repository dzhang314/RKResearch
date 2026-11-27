module

public import RKCert.ReviewedNative.DIRKRealIntegerFlagReceipts
public import RKCert.ReviewedNative.DIRKRealIntegerFlagRoots
public import RKCert.ReviewedNative.DIRKOrderTenSaturation

@[expose] public section

/-! The real-valued eleven-stage DIRK endpoint.
The column arithmetic, exact real root brackets, and finite grade-receipt
checks are independently kernel-verified. No floating-point approximations
or external decision axioms enter the theorem. -/
namespace RKResearch.Certified

open DIRKRealIntegerFlagReplay DIRKRealOrderTenIntegerData

/-- There is a literal lower triangular eleven-stage tableau over the
reals with full rooted order exactly ten. -/
theorem dirk_order_ten_eleven_stages_real :
    ∃ (U : Matrix (Fin 11) (Fin 11) ℝ) (w : Fin 11 → ℝ),
      U.IsLowerTriangular ∧ RKResearch.HasOrder 10 U w ∧ ¬ RKResearch.HasOrder 11 U w := by
  obtain ⟨x,y,z,h⟩ := DIRKRealOrderTenIntegerRoots.exists_roots
  exact ⟨A packet x y z,b packet x y z,lower packet x y z,
    order_ten h DIRKRealOrderTenIntegerChecks.receipts,
    no_order_eleven h DIRKRealOrderTenIntegerChecks.receipts⟩

/-- The previously reviewed field lower bound, now paired with the
eleven-stage real witness above. -/
theorem dirk_order_ten_real_stage_floor {s : Nat} {U : Matrix (Fin s) (Fin s) ℝ}
    {w : Fin s → ℝ} (hU : U.IsLowerTriangular) (hw : RKResearch.HasOrder 10 U w) :
    11 ≤ s :=
  Graded.CrossedOrderTen.stage_floor hU hw

end RKResearch.Certified

#print axioms RKResearch.Certified.dirk_order_ten_eleven_stages_real
#print axioms RKResearch.Certified.dirk_order_ten_real_stage_floor
