module

import RKCert.ReviewedNative.IndexedResidueMoments

open RKResearch.Certified.Graded.IndexedResidueMoments
open scoped BigOperators

universe u v w

section LiteralMap

variable {ι : Type v} [Fintype ι] {R : Type u} {S : Type w}
variable [CommSemiring R] [CommSemiring S]

/-- The target has exactly the same factorial and original index. -/
example (f : R →+* S) (x weights : ι → R) (k d qMax : ℕ)
    (h : ∀ q : ℕ, q ≤ qMax →
      (k.factorial : R) * ((d + q : ℕ) : R) * ((d + q + 1 : ℕ) : R) *
        (∑ i : ι, weights i * x i ^ q) = 1) :
    ∀ q : ℕ, q ≤ qMax →
      (k.factorial : S) * ((d + q : ℕ) : S) * ((d + q + 1 : ℕ) : S) *
        (∑ i : ι, f (weights i) * f (x i) ^ q) = 1 :=
  ClearedMoments.map_factorial_normalizer (x := x) (w := weights)
    (k := k) (d := d) (qMax := qMax) f h

/-- The input's single factorial-unit premise is exactly the paid window. -/
example (p : ℕ) :
    IsUnit (p.factorial : R) ↔ ∀ n : ℕ, 0 < n → n ≤ p → IsUnit (n : R) :=
  factorial_cast_isUnit_iff p

end LiteralMap

section LiteralFieldClient

variable {ι : Type v} [Fintype ι] {R : Type u} [CommRing R] [Nontrivial R]

/-- A field client receives the original finite family, exact target casts,
all the paid factorial units, and all paid positive nonzero casts. -/
example (x weights : ι → R) (k d qMax p : ℕ)
    (h : ClearedMoments x weights (k.factorial : R) d qMax)
    (hfac : IsUnit (p.factorial : R)) {C : Prop}
    (fieldClient : ∀ (K : Type u) [Field K] (x' weights' : ι → K),
      (∀ q : ℕ, q ≤ qMax →
        (k.factorial : K) * ((d + q : ℕ) : K) * ((d + q + 1 : ℕ) : K) *
          (∑ i : ι, weights' i * x' i ^ q) = 1) →
      (∀ n : ℕ, n ≤ p → IsUnit (n.factorial : K)) →
      (∀ n : ℕ, 0 < n → n ≤ p → (n : K) ≠ 0) → C) : C := by
  obtain ⟨I, hI, mapped, fac, paid⟩ := ClearedMoments.exists_maximal_residue h hfac
  let := hI
  let := Ideal.Quotient.field I
  have exactMapped : ClearedMoments (Ideal.Quotient.mk I ∘ x) (Ideal.Quotient.mk I ∘ weights)
      (k.factorial : R ⧸ I) d qMax := by
    simpa only [map_natCast] using mapped
  exact fieldClient (R ⧸ I) (Ideal.Quotient.mk I ∘ x) (Ideal.Quotient.mk I ∘ weights)
    exactMapped fac paid

end LiteralFieldClient

#check @RKResearch.Certified.Graded.IndexedResidueMoments.ClearedMoments.map
#check @RKResearch.Certified.Graded.IndexedResidueMoments.ClearedMoments.map_factorial_normalizer
#check @RKResearch.Certified.Graded.IndexedResidueMoments.factorial_cast_isUnit_iff
#check @RKResearch.Certified.Graded.IndexedResidueMoments.ClearedMoments.in_maximal_residue
#check @RKResearch.Certified.Graded.IndexedResidueMoments.ClearedMoments.exists_maximal_residue

#print axioms RKResearch.Certified.Graded.IndexedResidueMoments.ClearedMoments.map
#print axioms RKResearch.Certified.Graded.IndexedResidueMoments.ClearedMoments.map_factorial_normalizer
#print axioms RKResearch.Certified.Graded.IndexedResidueMoments.factorial_cast_isUnit_iff
#print axioms RKResearch.Certified.Graded.IndexedResidueMoments.ClearedMoments.in_maximal_residue
#print axioms RKResearch.Certified.Graded.IndexedResidueMoments.ClearedMoments.exists_maximal_residue
