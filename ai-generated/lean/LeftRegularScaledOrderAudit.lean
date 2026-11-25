import RKCert.ReviewedNative.FiniteScaledOrderCheck

open RKResearch RKResearch.Certified
open scoped Matrix

section Semiring

variable {ι R S : Type*} [Fintype ι] [CommSemiring R] [CommSemiring S]

example (A : Matrix ι ι R) (z : R) (t : FiniteRootedTree) :
    Φ t (z • A) = z^((t.order : ℕ)-1) • Φ t A :=
  Φ_matrix_smul A z t

example {A : Matrix ι ι R} {b : ι → R} {U : Matrix ι ι S} {w : ι → S}
    (f : R →+* S) {d e : R} {p : ℕ}
    (hA : A.map f = f d • U) (hb : f ∘ b = f e • w)
    (h : ∀ t : FiniteRootedTree, (t.order : ℕ) ≤ p →
      (t.factorial : R) * (b ⬝ᵥ Φ t A) = e*d^((t.order : ℕ)-1)) :
    (IsLeftRegular (f d) → IsLeftRegular (f e) → HasOrder p U w) ∧
      (IsUnit (f d) → IsUnit (f e) → HasOrder p U w) :=
  ⟨fun hd he => hasOrder_of_scaled_moments_of_leftRegular f hA hb hd he h,
    fun hd he => hasOrder_of_scaled_moments f hA hb hd he h⟩

end Semiring

section CheckedClient

variable {ι R S : Type*} [Fintype ι] [CommRing R] [CommRing S] [DecidableEq R]

example {A : Matrix ι ι R} {b : ι → R} {U : Matrix ι ι S} {w : ι → S}
    (f : R →+* S) {d e : R} {p : ℕ}
    {act : (ι → R) → (ι → R)} {out : (ι → R) → R}
    (hact : ∀ v, act v = A *ᵥ v) (hout : ∀ v, out v = b ⬝ᵥ v)
    (hA : A.map f = f d • U) (hb : f ∘ b = f e • w)
    (hd : IsUnit (f d)) (he : IsUnit (f e))
    (h : checkScaledOrder act out d e p = true) : HasOrder p U w :=
  hasOrder_of_scaled_check f hact hout hA hb hd he h

end CheckedClient

#print axioms RKResearch.Certified.Φ_matrix_smul
#print axioms RKResearch.Certified.hasOrder_of_scaled_moments_of_leftRegular
#print axioms RKResearch.Certified.hasOrder_of_scaled_moments
#print axioms RKResearch.Certified.hasOrder_of_scaled_check
