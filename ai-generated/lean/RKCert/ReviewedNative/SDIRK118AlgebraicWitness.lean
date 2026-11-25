module

public import RKCert.ReviewedNative.SDIRK118FieldDegreeTwelve
public import RKCert.ReviewedNative.SDIRK118VerifiedWitness
import RKCert.ReviewedNative.SDIRK118ScalarQuadraticSigns
import RKCert.ReviewedNative.SDIRK118OldGuardTables
import RKCert.ReviewedNative.SDIRK118AffineBoxReceipt

@[expose] public section

namespace RKResearch.Certified.PaidDefectBridge.SDIRK118

open Endpoint ScalarExistence

private theorem real_seed : ClaimPin.ScalarExistenceTarget := by
  have q := ScalarQuadraticSigns.quadratic_box_signs realMonomials realMonomials_standard
  exact scalarExistenceTarget_of_box_signs
    ⟨q, OldGuardTables.oldGuards realMonomials realMonomials_standard
      (fun s hs t ht => (q s hs t ht).1), AffineBoxReceipt.affine_box_signs⟩

/-- The literal eleven-stage real tableau can be defined over a
single algebraic ordered subfield of the reals. -/
theorem exists_strict_sdirk11_hasOrder8_over_algebraic_field : Subfield.CommonAlgebraicTarget :=
  Subfield.exists_algebraic_of_real_producers
    (literal_conditional_of_reverse LiteralReverseProducer.literal_reverse_leaves)
    real_seed realMonomials realMonomials_standard blockEquiv blockEquiv_ordered

/-- The coefficient field of the literal eleven-stage witness can be
chosen of finite degree at most twelve over the rationals. -/
theorem exists_strict_sdirk11_hasOrder8_over_field_degree_le_twelve : Subfield.DegreeTwelveTarget :=
  Subfield.exists_degreeTwelve_of_real_producers
    (literal_conditional_of_reverse LiteralReverseProducer.literal_reverse_leaves)
    real_seed realMonomials realMonomials_standard blockEquiv blockEquiv_ordered

end RKResearch.Certified.PaidDefectBridge.SDIRK118
