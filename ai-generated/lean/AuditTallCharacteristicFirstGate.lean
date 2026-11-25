module

public import RKCert.ReviewedNative.TallCharacteristicResponse

@[expose] public section

open RKResearch Polynomial RKResearch.Certified.TallFiniteResponse
open scoped Matrix Polynomial

variable {K : Type*} [Field K]
variable {s p : ℕ} {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K} {P Q : K[X]}

example (n : ℕ) (hn : s < n) : convolution (denominator A) (responseCoeff A b) n = 0 :=
  response_cutoff A b n hn

example : Fraction A b (numerator A b) (denominator A) := physical_fraction A b

example (h : Fraction A b P Q) (N : ℕ) :
    (X : K[X])^N ∣ Q * «prefix» (responseCoeff A b) N - P :=
  h.prefix_dvd N

example (hA : A.IsLowerTriangular) (h : Fraction A b P Q) (hc : IsCoprime Q P) :
    Q.Splits :=
  reduced_denominator_splits hA h hc

example (ho : HasOrder p A b) (h : Fraction A b P Q) (n : ℕ) (hn : n ≤ p) :
    convolution Q (exponentialCoeff K) n = P.coeff n :=
  paid_fraction_coeff ho h n hn

#print axioms response_cutoff
#print axioms physical_fraction
#print axioms Fraction.prefix_dvd
#print axioms reduced_denominator_splits
#print axioms paid_fraction_coeff
