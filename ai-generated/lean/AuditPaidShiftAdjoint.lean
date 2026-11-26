module

import RKCert.ReviewedNative.PaidShiftAdjoint

open RKResearch.ContextCompletion RKResearch.ContextCompletion.PaidShift
open RKResearch.Certified.Graded (primitive)
open Polynomial
open scoped Polynomial

/- The operations are the actual linear maps, with the negative shift on each. -/
example {K : Type*} [Field K] (γ : K) (W F : K[X]) :
    (shift γ : K[X] →ₗ[K] K[X]) F = primitive F - γ • F ∧
      (adjoint γ : K[X] →ₗ[K] K[X]) W = C (unitMoment W) - primitive W - γ • W :=
  ⟨shift_apply γ F, adjoint_apply γ W⟩

/- The one-step consumer pays only its stated degree budget. -/
example {K : Type*} [Field K] {p : ℕ} (units : PaidUnits K p) (γ : K)
    (W F : K[X]) (paid : W.natDegree + F.natDegree + 1 < p) :
    unitMoment (W * shift γ F) = unitMoment (adjoint γ W * F) :=
  unitMoment_shift_byParts units γ W F paid

/- Both sides of the iteration are the literal forward/test maps. -/
example {K : Type*} [Field K] {p : ℕ} (units : PaidUnits K p) (γ : K)
    (d : ℕ) (W F : K[X]) (paid : W.natDegree + F.natDegree + d < p) :
    unitMoment ((((adjoint γ : K[X] → K[X])^[d]) W) * F) =
      unitMoment (W * (((shift γ : K[X] → K[X])^[d]) F)) :=
  unitMoment_iterate_shift_byParts units γ d W F paid

/- A pure unary zero transports for an arbitrary polynomial, with no hull. -/
example {K : Type*} [Field K] {p : ℕ} (units : PaidUnits K p) (γ : K)
    (d : ℕ) (F : K[X]) (paid : F.natDegree + d < p)
    (forward : unitMoment (((shift γ : K[X] → K[X])^[d]) F) = 0) :
    unitMoment (pureUnaryTest γ d * F) = 0 :=
  unitMoment_pureUnary_cancel units γ d F paid forward

#print axioms RKResearch.ContextCompletion.PaidShift.shift_apply
#print axioms RKResearch.ContextCompletion.PaidShift.adjoint_apply
#print axioms RKResearch.ContextCompletion.PaidShift.unitMoment_shift_byParts
#print axioms RKResearch.ContextCompletion.PaidShift.unitMoment_iterate_shift_byParts
#print axioms RKResearch.ContextCompletion.PaidShift.unitMoment_pureUnary_cancel
