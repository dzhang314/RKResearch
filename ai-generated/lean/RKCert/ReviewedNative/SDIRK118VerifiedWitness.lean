module

public import RKCert.ReviewedNative.SDIRK118Endpoint
public import RKCert.ReviewedNative.SDIRK118LiteralReverseProducer
import RKCert.ReviewedNative.SDIRK118ScalarQuadraticSigns
import RKCert.ReviewedNative.SDIRK118OldGuardTables
import RKCert.ReviewedNative.SDIRK118AffineBoxReceipt

@[expose] public section

namespace RKResearch.Certified.PaidDefectBridge.SDIRK118

open Endpoint ScalarExistence

/-- A real eleven-stage strictly singly diagonally implicit method of
order at least eight. All stages have the same positive diagonal. -/
theorem exists_real_strict_sdirk11_hasOrder8 :
    ∃ (A : Matrix (Fin 11) (Fin 11) ℝ) (b : Fin 11 → ℝ) (γ : ℝ),
      0 < γ ∧ A.IsLowerTriangular ∧ (∀ i : Fin 11, A i i = γ) ∧ RKResearch.HasOrder 8 A b := by
  have q := ScalarQuadraticSigns.quadratic_box_signs realMonomials realMonomials_standard
  exact exists_real_strict_sdirk11_hasOrder8_of_producers
    (scalarExistenceTarget_of_box_signs
      ⟨q, OldGuardTables.oldGuards realMonomials realMonomials_standard
        (fun s hs t ht => (q s hs t ht).1), AffineBoxReceipt.affine_box_signs⟩)
    LiteralReverseProducer.literal_reverse_leaves

end RKResearch.Certified.PaidDefectBridge.SDIRK118
