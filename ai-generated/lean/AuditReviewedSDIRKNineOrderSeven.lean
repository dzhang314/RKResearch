import RKCert.ReviewedNative.SDIRKNineOrderSeven

open RKResearch RKResearch.Certified
open scoped Matrix

example :
    ∃ (A : Matrix (Fin 9) (Fin 9) ℝ) (b : Fin 9 → ℝ) (γ : ℝ),
      A.IsLowerTriangular ∧ (∀ i, A i i = γ) ∧ γ ≠ 0 ∧ HasOrder 7 A b :=
  strictSDIRK_order_seven_nine_stages_real

local notation "ℝₐ" => (algebraicClosure ℚ ℝ : Type)

example :
    ∃ (A : Matrix (Fin 9) (Fin 9) ℝₐ) (b : Fin 9 → ℝₐ) (γ : ℝₐ),
      A.IsLowerTriangular ∧ (∀ i, A i i = γ) ∧ γ ≠ 0 ∧ HasOrder 7 A b :=
  strictSDIRK_order_seven_nine_stages_realAlgebraic

#print axioms RKCert.ReviewedNative.IntegerHornerCertificate.checkLocal_sound
#print axioms RKCert.ReviewedNative.QuadraticHornerReplay.QExpr.checkVec_sound
#print axioms SDIRKNineReplay.catalogue_eq
#print axioms SDIRKNineReplay.all_moments
#print axioms SDIRKNineReplay.exists_realAlgebraic_rootPair
#print axioms SDIRKNineReplay.order_seven
#print axioms strictSDIRK_order_seven_nine_stages_real
#print axioms strictSDIRK_order_seven_nine_stages_realAlgebraic
