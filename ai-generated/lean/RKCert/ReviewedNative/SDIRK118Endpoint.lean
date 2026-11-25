module

public import RKCert.ReviewedNative.SDIRK118ScalarCalibration
public import Mathlib.Algebra.Polynomial.Basis
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

noncomputable section

namespace RKResearch.Certified.PaidDefectBridge.SDIRK118.Endpoint

open RKResearch
open RKResearch.Certified.PaidDefectBridge.SDIRK118.ClaimPin
open RKResearch.Certified.PaidDefectBridge.SDIRK118.ConditionalFin11
open RKResearch.Certified.PaidDefectBridge.SDIRK118.ForwardCubics
open RKResearch.Certified.PaidDefectBridge.SDIRK118.ScalarBindings
open RKResearch.Certified.PaidDefectBridge.SDIRK118.ScalarCalibration

/-- Standard monomials of the actual coefficient field, not an
existentially chosen basis or coefficient field. -/
def realMonomials : MonomialBasis := Polynomial.basisMonomials ℝ

theorem realMonomials_standard : standardPowers realMonomials := by
  intro n
  change Polynomial.monomial n (1 : ℝ) = Polynomial.X ^ n
  exact Polynomial.monomial_one_right_eq_X_pow n

def blockEquiv : (Fin 4 ⊕ Fin 8) ≃ Fin 12 := finSumFinEquiv

theorem blockEquiv_ordered : orderedBlocks blockEquiv :=
  ⟨fun _ => rfl, fun _ => rfl⟩

/-- The remaining reverse donor producer, on the already fixed literal
geometry and exact seed. This is not a free reverse-matrix choice. -/
def ReverseProducer : Prop :=
  ∀ (M : MonomialBasis), standardPowers M →
    ∀ (s t cStar : ℝ), ExactScalarSeed M s t cStar →
      ReverseLeaves (geometry M s t cStar) (reverseClock s t) (reverseG s)

/-- Real scalar and forward producers both come from the same seed.
No residual denominator is an independent premise at this boundary. -/
theorem literal_conditional_of_reverse (reverse : ReverseProducer) : ConditionalTarget := by
  refine conditionalTarget_of_leafProducer ?_
  intro M hm s t c seed
  exact ⟨literal_scalar_leaves M hm s t c seed,
    literal_forward_leaves_of_guards M hm s t c seed (literal_residual_pivot M hm s t c seed),
    reverse M hm s t c seed⟩

/-- Headline target after the separate scalar existence and literal reverse
checks. Strict SDIRK here means lower triangular with the same nonzero
diagonal; the witness in fact has positive common diagonal. HasOrder 8 is
order at least eight, not an assertion of exact order or stage minimality. -/
theorem exists_real_strict_sdirk11_hasOrder8_of_producers
    (hex : ScalarExistenceTarget) (reverse : ReverseProducer) :
    ∃ (A : Matrix (Fin 11) (Fin 11) ℝ) (b : Fin 11 → ℝ) (γ : ℝ),
      0 < γ ∧ A.IsLowerTriangular ∧ (∀ i : Fin 11, A i i = γ) ∧ HasOrder 8 A b :=
  close_from_two_proofs (literal_conditional_of_reverse reverse) hex
    realMonomials realMonomials_standard blockEquiv blockEquiv_ordered

end RKResearch.Certified.PaidDefectBridge.SDIRK118.Endpoint
