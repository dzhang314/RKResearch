module

public import RKCert.ReviewedNative.ERK10FixedQ29AdicRemainderUnit
public import RKCert.ReviewedNative.ERK10FixedQ29AdicLimit

@[expose] public section

namespace RKResearch.Certified.ERK10FixedQ29Adic.Nonlinear

open Polynomial
open scoped Polynomial
open Digits

/-- The chosen compatible point supports all of the exact fixed-q scalar
closure identities simultaneously. This does not construct the physical
Runge–Kutta matrix or assert order. -/
theorem exact_nonlinear_limit :
    ∃ c a b : Z29Limit,
      (decic Z29Limit).eval c = 0 ∧ reduce c = 2 ∧ origin c = 0 ∧
      (headQuadratic c).eval a = 0 ∧ reduce a = 11 ∧
      (headQuadratic c).eval b = 0 ∧ reduce b = 20 ∧ b = headSum c-a ∧
      reduce (hTail c) = 22 ∧ reduce (fTail c) = 7 ∧ reduce (eTail c) = 27 ∧
      PaidHead c ∧
      (actualQ1 c).eval (hTail c) = phaseValue c (hTail c) ∧
      reduce ((bRemainder c).coeff 0) = 4 ∧ IsUnit ((bRemainder c).coeff 0) ∧
      (actualMu c*closureU c-X*(1-X)*actualQ1 c) %ₘ actualD7 c = 0 ∧
      (closureU c).eval 15 = -1 ∧ (closureU c).natDegree ≤ 4 := by
  obtain ⟨c,a,b,hp,hr,ho,ha,har,hb,hbr,hab,hh,hf,he,hpaid⟩ := scalar_existence_limit
  refine ⟨c,a,b,hp,hr,ho,ha,har,hb,hbr,hab,hh,hf,he,hpaid,?_,
    ResiduePivot.residueB0 reduce c hp hr,ResiduePivot.paidB0 reduce c hp hr,
    closure_remainder_zero reduce c hp hr,closure_host reduce c hr,closure_degree c⟩
  rw [actualQ1_eval,exact_h_phase reduce c hp hr]

end RKResearch.Certified.ERK10FixedQ29Adic.Nonlinear

#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Nonlinear.exact_nonlinear_limit
