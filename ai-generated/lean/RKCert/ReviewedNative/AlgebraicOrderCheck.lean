module

public import RKCert.ReviewedNative.FiniteOrderCheck
public import Mathlib.Algebra.Ring.Basic

public section

/-!
# Finite order certificate on a vanishing relation

A parametric tableau can be checked by factoring each finite residual by
one relation in its coefficient ring. At a root, the same reviewed order
checker turns these factorizations into a native `HasOrder` proof.
-/

namespace RKResearch.Certified

open scoped Matrix

variable {ι R : Type*} [Fintype ι] [CommRing R]

/-- Every listed normalized residual is divisible by a relation that
vanishes. The finite list is the same one used by `checkOrder`. -/
theorem hasOrder_of_finite_residual_dvd
    (A : Matrix ι ι R) (b : ι → R) (p : ℕ) {r : R} (hr : r = 0)
    (h : ∀ n < p, ∀ t ∈ treesOfOrderSucc n,
      r ∣ (t.factorial : R) * (b ⬝ᵥ Φ t A) - 1) :
    HasOrder A b p := by
  classical
  apply (checkOrder_iff A b p).mp
  simp only [checkOrder, List.all_eq_true, List.mem_range, decide_eq_true_eq]
  intro n hn t ht
  obtain ⟨q, hq⟩ := h n hn t ht
  exact sub_eq_zero.mp (by simpa [hr] using hq)

end RKResearch.Certified
