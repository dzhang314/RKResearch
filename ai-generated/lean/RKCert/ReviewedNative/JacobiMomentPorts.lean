module

public import RKCert.NodalPrimitive
public import Mathlib.RingTheory.Polynomial.ShiftedLegendre

@[expose] public section

/-! # Scalar inputs for adjacent signed Jacobi bands

The precision is algebraic. A moment means the formal primitive with zero
constant, evaluated at one; no real order or analytic integral is used. -/
namespace RKCert.ReviewedNative.JacobiMoments
open Polynomial RKCert.Endpoint

variable {K : Type*} [Field K]
noncomputable section

/-- The signed derivative of the integer shifted Legendre polynomial, in K. -/
def signedSlope (K : Type*) [Field K] (m : ℕ) : K[X] :=
  C ((-1 : K)^m) * ((shiftedLegendre m).derivative.map (Int.castRingHom K))

/-- Adjacent unit moments of X D agree for the indicated r+1 exponents. -/
def MomentDifferences (D : K[X]) (r : ℕ) : Prop :=
  ∀ k : Fin (r+1),
    (formalPrimitive (X^k.val * (X*D))).eval 1 =
    (formalPrimitive (X^(k.val+1) * (X*D))).eval 1

end
end RKCert.ReviewedNative.JacobiMoments
