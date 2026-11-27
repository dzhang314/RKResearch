module

public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8BezoutDefectReceipt

open Polynomial

/-- In the coprime quadratic chart the degree-two dual defect profile is
a nonzero scalar multiple of the denominator. The same scalar identifies
the degree-five dual squared-defect profile with the numerator. -/
theorem sharedScalar {K : Type*} [Field K] {p q r s : K[X]}
    (hpq : IsCoprime p q) (hq : q.natDegree=2) (hr : r.natDegree≤2)
    (hr0 : r≠0) (hid : q*s=r*p) :
    ∃ a : K, a≠0 ∧ r=C a*q ∧ s=C a*p := by
  have hq0 : q≠0 := by
    intro h
    simp [h] at hq
  have hd : q ∣ r*p := ⟨s,hid.symm⟩
  obtain ⟨u,hu⟩ := hpq.symm.dvd_of_dvd_mul_right hd
  have hu0 : u≠0 := by
    intro h
    exact hr0 (by simp [hu,h])
  have h0 : u.natDegree=0 := by
    rw [hu,natDegree_mul hq0 hu0,hq] at hr
    omega
  have hC : u=C (u.coeff 0) := eq_C_of_natDegree_eq_zero h0
  have hr' : r=C (u.coeff 0)*q := calc
    r=q*u := hu
    _=q*C (u.coeff 0) := congrArg (q*·) hC
    _=C (u.coeff 0)*q := mul_comm _ _
  refine ⟨u.coeff 0,?_,hr',mul_left_cancel₀ hq0 ?_⟩
  · intro hz
    exact hr0 (by rw [hr',hz]; simp)
  rw [hid,hr']
  ring

end RKCert.ReviewedNative.SDIRK8BezoutDefectReceipt
