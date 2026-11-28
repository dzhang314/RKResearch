module

public import Mathlib.Algebra.Polynomial.Eval.Degree

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8GuardedFiber

open Polynomial

/-- Exact pseudo-division may remove a factor only when its value on
the actual branch is nonzero. The multiplying coefficient need not be a unit. -/
theorem evalZeroOfGuardedPseudoDivision
    {R K : Type*} [CommRing R] [Field K] (ι : R →+* K)
    (p d q : R[X]) (c : R) (x : K) (he : C c * p = d * q)
    (hp : p.eval₂ ι x = 0) (hd : d.eval₂ ι x ≠ 0) :
    q.eval₂ ι x = 0 := by
  have h := congrArg (fun v : R[X] => v.eval₂ ι x) he
  rw [eval₂_mul, eval₂_mul, hp, mul_zero] at h
  exact (mul_eq_zero.mp h.symm).resolve_left hd

/-- A surviving leading coefficient licenses degree-preserving reduction
on an exact branch, including a branch already reduced in degree. -/
theorem natDegreeOfGuardedReduction
    {R K : Type*} [CommRing R] [Field K] (ρ : R →+* K) (p : R[X])
    (h : ρ p.leadingCoeff ≠ 0) :
    (p.map ρ).natDegree = p.natDegree :=
  natDegree_map_of_leadingCoeff_ne_zero ρ h

end RKCert.ReviewedNative.SDIRK8GuardedFiber

#print axioms RKCert.ReviewedNative.SDIRK8GuardedFiber.evalZeroOfGuardedPseudoDivision
#print axioms RKCert.ReviewedNative.SDIRK8GuardedFiber.natDegreeOfGuardedReduction
