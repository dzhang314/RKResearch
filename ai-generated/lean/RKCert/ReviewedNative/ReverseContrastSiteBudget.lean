module

public import RKCert.ReviewedNative.ReversePhysicalPorts

import Mathlib.Tactic.Ring

@[expose] public section

/-! # Actual contrast-site count from paid reflected moments

Testing with the true support hull times a monomial detects the
polynomial left after imposing its physical zeros. The unit Cauchy
detector needs characteristic zero but no positivity or ordering. -/
namespace RKResearch.Certified.Graded.Reverse.Thin

open RKResearch Polynomial RKCert.Endpoint RKCert.Endpoint.WeightedClock
open RKResearch.Certified.Graded.NativeMoments

noncomputable section
variable {K : Type*} [Field K] [CharZero K] {s p : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}

/-- If there were at most r actual contrast sites, the nodal hull would
pay a full X-weighted Cauchy test of the nonzero product Q times that
hull. Neither trace fitting nor strict triangularity is an input. -/
theorem reverse_contrast_sites_gt_of_paid_moments (ho : HasOrder p A b)
    {Q P : K[X]} {r : ℕ} (qn : Q ≠ 0)
    (qpay : 2 * Q.natDegree + 2 * r + 2 ≤ p)
    (ppay : Q.natDegree + P.natDegree + 2 * r + 3 ≤ p) :
    r < (weightedSites (reflectedClock A) (reverseContrast A b Q P)).card := by
  classical
  let W := reverseContrast A b Q P
  let S := weightedSites (reflectedClock A) W
  let Z := nodalHull S
  change r < S.card
  by_contra! small
  have zd : Z.natDegree ≤ r := (natDegree_nodalHull S).le.trans small
  have degree : (Q * Z).natDegree ≤ Q.natDegree + r :=
    natDegree_mul_le.trans (Nat.add_le_add_left zd Q.natDegree)
  apply mul_ne_zero qn (monic_nodalHull S).ne_zero
  refine x_moments_detect degree ?_
  intro i
  let H : K[X] := X ^ i.val * Z
  have hd : H.natDegree ≤ Q.natDegree + 2 * r := by
    have m := natDegree_mul_le (p := (X : K[X]) ^ i.val) (q := Z)
    rw [natDegree_X_pow] at m
    have hi := i.isLt
    change ((X : K[X]) ^ i.val * Z).natDegree ≤ Q.natDegree + 2 * r
    omega
  have vanishes (a : K) (ha : a ∈ S) : H.eval a = 0 := by
    have root : Z.eval a = 0 := nodalHull_eval_of_mem ha
    simp only [H, eval_mul, root, mul_zero]
  have sparse := reverse_contrast_vanishes (A := A) W H vanishes
  have paid := reverse_contrast_moment ho Q P H (by omega) (by omega)
  have zero : (primitive (H * (X * Q))).eval 1 = 0 := paid.symm.trans sparse
  have regroup : H * (X * Q) = X ^ i.val * (X * (Q * Z)) := by
    dsimp only [H]
    ring
  rw [regroup] at zero
  exact zero

end
end RKResearch.Certified.Graded.Reverse.Thin
