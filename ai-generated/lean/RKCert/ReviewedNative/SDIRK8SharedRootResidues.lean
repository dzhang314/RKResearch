module

public import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8SharedRootResidues

open Polynomial

/-- A common root gives double divisibility in each residue input, including
after reduction by the squared denominator. -/
theorem commonRootDvd {R : Type*} [CommRing R] (p q : R[X]) (r : R)
    (hp : p.IsRoot r) (hq : q.IsRoot r) :
    (X-C r)^2 ∣ (q*p) %ₘ q^2 ∧
    (X-C r)^2 ∣ (X*q*p) %ₘ q^2 ∧
    (X-C r)^2 ∣ p^2 %ₘ q^2 ∧
    (X-C r)^2 ∣ (X*p^2) %ₘ q^2 := by
  obtain ⟨u,hu⟩ := dvd_iff_isRoot.mpr hp
  obtain ⟨v,hv⟩ := dvd_iff_isRoot.mpr hq
  subst p
  subst q
  have hdiv : (X-C r)^2 ∣ ((X-C r)*v)^2 := ⟨v^2,by ring⟩
  have pass {f : R[X]} (hf : (X-C r)^2 ∣ f) :
      (X-C r)^2 ∣ f %ₘ (((X-C r)*v)^2) := by
    rw [modByMonic_eq_sub_mul_div]
    exact dvd_sub hf (hdiv.trans (dvd_mul_right ..))
  exact ⟨pass ⟨v*u,by ring⟩,pass ⟨X*v*u,by ring⟩,
    pass ⟨u^2,by ring⟩,pass ⟨X*u^2,by ring⟩⟩

/-- A divisible residue of a squared monic quadratic is its squared linear
factor times a polynomial of degree at most one. This is the two-dimensional
space underlying the shared-root saturation check. -/
theorem divisibleQuadraticResidue {K : Type*} [Field K] (f q : K[X]) (r : K)
    (hm : q.Monic) (hd : q.natDegree=2) (h : (X-C r)^2 ∣ f %ₘ q^2) :
    ∃ a : K[X], a.natDegree ≤ 1 ∧ f %ₘ q^2 = (X-C r)^2*a := by
  obtain ⟨a,ha⟩ := h
  refine ⟨a,?_,ha⟩
  by_cases hz : a=0
  · simp [hz]
  have h4 : (q^2).natDegree=4 := by rw [natDegree_pow,hd]
  have h1 : q^2 ≠ 1 := by
    intro h1
    rw [h1,natDegree_one] at h4
    omega
  have hv := natDegree_modByMonic_lt f (hm.pow 2) h1
  rw [ha,natDegree_mul (pow_ne_zero _ (X_sub_C_ne_zero _)) hz,
    natDegree_pow,natDegree_X_sub_C,h4] at hv
  omega

end RKCert.ReviewedNative.SDIRK8SharedRootResidues
