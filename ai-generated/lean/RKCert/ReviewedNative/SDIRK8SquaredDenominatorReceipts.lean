module

public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8SquaredDenominatorReceipts

open Polynomial

/-- The two lifts of each denominator-residue direction are independent.
This is the kernel argument for the square-denominator moment chart; it
does not assume that the denominator splits or has distinct roots. -/
theorem squared_denominator_independent {K : Type*} [Field K]
    {p q r s : K[X]} (hpq : IsCoprime p q) (hq : q ≠ 0)
    (hr : r.degree < q.degree) (hs : s.degree < q.degree)
    (h : q^2 ∣ r*p^2 + q*s*p) : r=0 ∧ s=0 := by
  have hq₂ : q ∣ q^2 := ⟨q, pow_two q⟩
  have hp : q ∣ r*p^2 := by
    have hA := hq₂.trans h
    have hB : q ∣ q*s*p := ⟨s*p,by ring⟩
    convert dvd_sub hA hB using 1
    ring
  have hh : IsCoprime q (p^2) := (hpq.pow_left (m := 2)).symm
  have hz : r=0 := eq_zero_of_dvd_of_degree_lt (hh.dvd_of_dvd_mul_right hp) hr
  refine ⟨hz,?_⟩
  rw [hz,zero_mul,zero_add,pow_two] at h
  have hsp : q ∣ s*p := by
    obtain ⟨z,hz⟩ := h
    refine ⟨z,mul_left_cancel₀ hq ?_⟩
    simpa [mul_assoc] using hz
  exact eq_zero_of_dvd_of_degree_lt (hpq.symm.dvd_of_dvd_mul_right hsp) hs

/-- The four moment inputs \(p^2,Xp^2,qp,Xqp\) are independent modulo
\(q^2\) for a coprime quadratic denominator. This statement uses
general polynomial degrees rather than an actual node list. -/
theorem squared_denominator_flags {K : Type*} [Field K]
    {p q : K[X]} (hpq : IsCoprime p q) (hq : q.degree=2)
    (a b c d : K)
    (h : q^2 ∣ (C a+C b*X)*p^2+q*(C c+C d*X)*p) :
    (C a+C b*X : K[X])=0 ∧ (C c+C d*X : K[X])=0 := by
  have hq0 : q≠0 := by
    intro hzero
    simp [hzero] at hq
  have hdeg (e f : K) : (C e+C f*X : K[X]).degree < q.degree := by
    rw [hq]
    have hA : (C e : K[X]).degree ≤ (1 : ℕ) :=
      degree_C_le.trans (by decide)
    have hB' : (C f*X : K[X]).degree ≤ (0 : WithBot ℕ) + 1 :=
      degree_mul_le_of_le degree_C_le (by rw [degree_X])
    have hB : (C f*X : K[X]).degree ≤ (1 : ℕ) := by simpa using hB'
    exact lt_of_le_of_lt (degree_add_le_of_degree_le hA hB) (by decide)
  exact squared_denominator_independent hpq hq0 (hdeg a b) (hdeg c d) h

end RKCert.ReviewedNative.SDIRK8SquaredDenominatorReceipts
