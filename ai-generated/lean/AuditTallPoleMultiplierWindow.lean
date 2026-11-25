module

import RKCert.ReviewedNative.TallPoleMultiplierWindow

open RKResearch RKResearch.Certified.TallFiniteResponse Polynomial
open scoped Matrix Polynomial

variable {K : Type*} [Field K] [CharZero K] {Q V B P : K[X]} {d s p : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}

example (h : PoleMultiplier Q d V B) (j : ℕ)
    (hw : ∀ i : ℕ, i ≤ d → expConvolution Q (j+1+i) = 0) :
    expConvolution Q j = 0 := h.backward j hw

example (h : PoleMultiplier Q d V B) (hQ : Q.coeff 0 = 1) (n : ℕ) :
    ¬ (∀ i : ℕ, i ≤ d → expConvolution Q (n+i) = 0) := h.not_zero_window hQ n

example (hf : Fraction A b P Q) (h : PoleMultiplier Q d V B) (ho : HasOrder p A b) :
    p ≤ P.natDegree+d := hf.order_le_num_add_of_multiplier h ho

/-- No degree-`<0` premise: the pole-free edge computes the same bound. -/
example (hf : Fraction A b P (1 : K[X])) (ho : HasOrder p A b) : p ≤ P.natDegree := by
  have hm : PoleMultiplier (1 : K[X]) 0 (1 : K[X]) (0 : K[X]) := by
    constructor <;> simp [Polynomial.coeff_one]
  simpa only [Nat.add_zero] using hf.order_le_num_add_of_multiplier hm ho

#print axioms PoleMultiplier.of_boundary
#print axioms PoleMultiplier.backward
#print axioms PoleMultiplier.not_zero_window
#print axioms PoleMultiplier.order_le_num_add_of_coeff_prefix
#print axioms Fraction.order_le_num_add_of_multiplier
