import RKCert.ReviewedNative.PaidPositiveDefectObstruction

open RKResearch.Certified.Graded
open scoped Matrix

section

variable {ι K : Type*} [Fintype ι] [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A : Matrix ι ι K} {b : ι → K} {p g : ℕ}

example (ho : RKResearch.HasOrder p A b) (pay : g + g + 1 ≤ p)
    (hb : ∀ i, 0 ≤ b i) (v : ι → K) (hv : v ∈ zeroSpace A g) :
    ∀ i, b i * v i = 0 :=
  paid_defect_weighted_zero_of_nonneg ho pay hb hv

example (ho : RKResearch.HasOrder p A b) (pay : g + g + 2 ≤ p)
    (links : ∀ i j, 0 ≤ b i * A i j) (q : ι → K) (hq : q ∈ zeroSpace A g) :
    (∀ i j, (b i * A i j) * q j = 0) ∧
      (∀ i, b i * (A *ᵥ q) i = 0) := by
  simpa only [mat_apply] using paid_donor_links_and_outgoing_zero ho pay links hq

example (ho : RKResearch.HasOrder p A b) (pay : g + g + 3 ≤ p)
    (hb : ∀ i, 0 ≤ b i) (q : ι → K) (hq : q ∈ zeroSpace A g) :
    ∀ i, b i * (A *ᵥ q) i = 0 := by
  simpa only [mat_apply] using paid_outgoing_weighted_zero_of_nonneg ho pay hb hq

end

#print axioms RKResearch.Certified.Graded.paid_defect_weighted_zero_of_nonneg
#print axioms RKResearch.Certified.Graded.paid_donor_links_and_outgoing_zero
#print axioms RKResearch.Certified.Graded.paid_outgoing_weighted_zero_of_nonneg
