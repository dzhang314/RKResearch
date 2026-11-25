import RKCert.ReviewedNative.SDIRK118VerifiedWitness

open RKResearch
open RKResearch.Certified.PaidDefectBridge.SDIRK118

example : ∃ (A : Matrix (Fin 11) (Fin 11) ℝ) (b : Fin 11 → ℝ) (γ : ℝ),
    0 < γ ∧ A.IsLowerTriangular ∧ (∀ i : Fin 11, A i i = γ) ∧ HasOrder 8 A b :=
  exists_real_strict_sdirk11_hasOrder8

#print axioms exists_real_strict_sdirk11_hasOrder8
#print axioms LiteralReverseProducer.literal_reverse_leaves
#print axioms ScalarQuadraticSigns.quadratic_box_signs
#print axioms OldGuardTables.oldGuards
#print axioms AffineBoxReceipt.affine_box_signs
