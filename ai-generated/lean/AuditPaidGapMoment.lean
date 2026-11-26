module

import RKCert.ReviewedNative.PaidGapMoment

open RKResearch RKResearch.Certified.Graded.PaidGapMoment
open scoped Matrix BigOperators

section

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]

/-- The physical commutator uses the matrix row sums and no compensating term. -/
example (A : Matrix ι ι K) :
    clockComm A =
      Matrix.diagonal (A *ᵥ (1 : ι → K)) * A -
        A * Matrix.diagonal (A *ᵥ (1 : ι → K)) :=
  rfl

/-- Literal row-weighted, signed, denominator-cleared pair sum. -/
example {A : Matrix ι ι K} {b : ι → K} {p h q : ℕ}
    (ho : HasOrder p A b) (positive : 0 < h) (pay : 2 * h + q + 1 ≤ p) :
    ((2 * h - 1).factorial : K) * ((2 * h + q : ℕ) : K) *
      ((2 * h + q + 1 : ℕ) : K) *
        (∑ i : ι, ∑ j : ι, b i *
          ((Matrix.diagonal (A *ᵥ (1 : ι → K)) * A -
            A * Matrix.diagonal (A *ᵥ (1 : ι → K))) ^ h) i j *
          ((A *ᵥ (1 : ι → K)) i - (A *ᵥ (1 : ι → K)) j) ^ q) = 1 :=
  paid_gapMoment ho positive pay

/-- The ordinary field readout is justified by the cleared equation itself. -/
example {A : Matrix ι ι K} {b : ι → K} {p h q : ℕ}
    (ho : HasOrder p A b) (positive : 0 < h) (pay : 2 * h + q + 1 ≤ p) :
    gapMoment A b h q =
      1 / (((2 * h - 1).factorial : K) * ((2 * h + q : ℕ) : K) *
        ((2 * h + q + 1 : ℕ) : K)) := by
  let den : K := ((2 * h - 1).factorial : K) * ((2 * h + q : ℕ) : K) *
    ((2 * h + q + 1 : ℕ) : K)
  have hclear : den * gapMoment A b h q = 1 := paid_gapMoment ho positive pay
  have hden : den ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hclear
    exact (zero_ne_one : (0 : K) ≠ 1) hclear
  change gapMoment A b h q = 1 / den
  exact (eq_div_iff hden).2 ((mul_comm _ _).trans hclear)

end

#check @RKResearch.Certified.Graded.PaidGapMoment.clockComm
#check @RKResearch.Certified.Graded.PaidGapMoment.gapMoment
#check @RKResearch.Certified.Graded.PaidGapMoment.paid_gapMoment

#print axioms RKResearch.Certified.Graded.PaidGapMoment.clockComm
#print axioms RKResearch.Certified.Graded.PaidGapMoment.gapMoment
#print axioms RKResearch.Certified.Graded.PaidGapMoment.paid_gapMoment
