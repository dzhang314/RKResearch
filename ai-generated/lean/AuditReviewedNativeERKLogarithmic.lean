module
import RKCert.ReviewedNative.ERKLogarithmic

open RKResearch RKResearch.Certified.Graded Module
universe u

section Field
variable {K : Type u} [Field K] [CharZero K] {s p j : ℕ}
    {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
    (ha : ∀ i k, i ≤ k → A i k=0)

example (h : HasOrder A b p) (j5 : 5≤j) (pay : 4*j≤p) :
    finrank K (zeroSpace A j)+j+1≤finrank K (zeroSpace A (2*j)) :=
  erk_doubling_rank_surplus ha h j5 pay

example (h : HasOrder A b 20) : 11≤finrank K (zeroSpace A 10) := by
  have first := grade_five_surplus_of_reviewed_order ha h (by decide)
  have next := erk_doubling_rank_surplus ha h (j:=5) (by decide) (by decide)
  simp only [Nat.reduceMul] at next
  omega

example (h : HasOrder A b 40) : 61≤s :=
  erk_logarithmic_field_dyadic ha h 2 (by decide)
end Field

section Ring
variable {R : Type u} [CommRing R] [CharZero R] {s p : ℕ}
    {A : Matrix (Fin s) (Fin s) R} {b : Fin s → R} (ha : ∀ i k, i ≤ k → A i k=0)

example (h : HasOrder A b p) (hp : 10≤p) : (3*p+1)/2-1+Nat.log 2 (p/10)≤s :=
  h.erk_logarithmic_stages ha hp

example (h : HasOrder A b 20) : 30≤s := h.erk_order_twenty_charZero_stages ha
example (h : HasOrder A b 40) : 61≤s := h.erk_logarithmic_stages ha (by decide)
example (h : HasOrder A b 80) : 122≤s := h.erk_logarithmic_stages ha (by decide)
end Ring

#check RKResearch.HasOrder.erk_logarithmic_stages
#check RKResearch.HasOrder.erk_order_twenty_charZero_stages
#print axioms RKCert.ReviewedNative.TwoKnot.twoEndpointJacobi
#print axioms RKCert.ReviewedNative.TwoKnot.physical_jacobi_gate
#print axioms HeadContrast.first_unmatched_block
#print axioms HeadContrast.head_contrast_at_physical_row
#print axioms HeadContrast.no_disjoint_polynomial_head_doubling
#print axioms no_explicit_doubling_head
#print axioms erk_doubling_rank_surplus
#print axioms erk_logarithmic_field_dyadic
#print axioms RKResearch.HasOrder.erk_logarithmic_stages
#print axioms RKResearch.HasOrder.erk_order_twenty_charZero_stages
