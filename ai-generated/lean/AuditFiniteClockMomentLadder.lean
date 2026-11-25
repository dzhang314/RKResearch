module

import RKCert.ReviewedNative.FiniteClockMomentLadder

open Polynomial
open scoped BigOperators Classical

set_option autoImplicit false
universe u
variable {K : Type u} [Field K]

example {H : Finset K} {count : ℕ} (mass : K → K) (size : H.card ≤ count)
    (tests : ∀ k : ℕ, k < count → (∑ x ∈ H, mass x * x ^ k) = 0) :
    ∀ a ∈ H, mass a = 0 := by
  apply RKCert.ReviewedNative.FiniteClockMoments.mass_zero_of_monomials H mass size
  intro k hk
  simpa only [RKCert.ReviewedNative.FiniteClockMoments.moment_apply,
    Polynomial.eval_pow, Polynomial.eval_X] using tests k hk

example {H T S : Finset K} {D : ℕ} (mass defect : K → K)
    (sub : S ⊆ T) (base : T.card ≤ D + 1)
    (law : ∀ Q : K[X], Q.natDegree ≤ D →
      (∑ x ∈ H, mass x * Q.eval x) = ∑ x ∈ T, defect x * Q.eval x) :
    (∀ a ∈ S, defect a = 0) ↔ ∀ k : ℕ, k < D + 1 - (T \ S).card →
      (∑ x ∈ H, (mass x * (RKCert.Endpoint.nodalHull (T \ S)).eval x) * x ^ k) = 0 := by
  have test (Q : K[X]) (hQ : Q.natDegree ≤ D) :
      RKCert.ReviewedNative.FiniteClockMoments.moment H mass Q =
        RKCert.ReviewedNative.FiniteClockMoments.moment T defect Q := by
    simpa only [RKCert.ReviewedNative.FiniteClockMoments.moment_apply] using law Q hQ
  exact (RKCert.ReviewedNative.FiniteClockMoments.zero_on_stops_iff_tilted_tests
    (H := H) (D := D) mass defect sub base test).trans
      (RKCert.ReviewedNative.FiniteClockMoments.tiltedTests_iff_sums H (T \ S) mass
        (RKCert.ReviewedNative.FiniteClockMoments.paidCount T S D))
