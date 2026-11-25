module

public import RKCert.ReviewedNative.OrderedAlternationDegree
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.FiniteOrderedSigns

open Polynomial
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Discard a square factor by transporting the already extracted
nonzero alternating witness. No assumption on the other samples. -/
theorem HasAlternationsOn.of_mul_sq {P T : K[X]} {S : Set K} {m : ℕ}
    (hs : HasAlternationsOn (P*T^2) S m) : HasAlternationsOn P S m := by
  obtain ⟨xs, inc, inside, alt, low⟩ := hs.alternating_samples
  refine HasAlternationsOn.of_alternating_samples inc inside ⟨?_, ?_⟩ low
  · intro x hx z
    apply alt.nonzero x hx
    simp only [eval_mul, eval_pow, z, zero_mul]
  · apply alt.jumps.imp
    intro x y opposite
    have pair :
        (P*T^2).eval x*(P*T^2).eval y =
          (P.eval x*P.eval y)*((T.eval x)^2*(T.eval y)^2) := by
      simp only [eval_mul, eval_pow]
      ring
    rw [pair] at opposite
    by_contra! same
    exact (not_lt_of_ge (mul_nonneg same
      (mul_nonneg (sq_nonneg _) (sq_nonneg _)))) opposite

end RKCert.ReviewedNative.FiniteOrderedSigns
