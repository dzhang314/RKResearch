module

import RKCert.ReviewedNative.DiagonalTreeShiftOrder

/-! Typed clients for the checked strict-order correction and first failure.
The independent matrix consumer is not imported. -/
open RKResearch RKResearch.DiagonalTreeShift

section Semiring

variable (R : Type*) [CommSemiring R]

example (a : R) (t : FiniteRootedTree) :
    ∃ e ∈ below R ((t.order : ℕ) - 1), expand R a t = atom R t + e :=
  expand_eq_atom_add_lower R a t

example {V : Type*} [AddCommMonoid V] [Module R V]
    (a : R) (f g : FiniteRootedTree → V) (t : FiniteRootedTree)
    (same : ∀ u, (u.order : ℕ) < (t.order : ℕ) → f u = g u) :
    ∃ c, transform R a f t = f t + c ∧ transform R a g t = g t + c :=
  same_correction R a f g t same

example {V : Type*} [AddCancelCommMonoid V] [Module R V]
    (a : R) (f g : FiniteRootedTree → V) (t : FiniteRootedTree)
    (same : ∀ u, (u.order : ℕ) < (t.order : ℕ) → f u = g u) :
    transform R a f t = transform R a g t ↔ f t = g t :=
  transform_at_eq_iff R a f g t same

end Semiring

section Ring

variable (S : Type*) [CommRing S]
variable {V : Type*} [AddCancelCommMonoid V] [Module S V]

example (a : S) (n : ℕ) (f g : FiniteRootedTree → V) :
    (∀ t, (t.order : ℕ) ≤ n → transform S a f t = transform S a g t) ↔
      (∀ t, (t.order : ℕ) ≤ n → f t = g t) :=
  agreesThrough_transform_iff S a n f g

example (a : S) (n : ℕ) (f g : FiniteRootedTree → V) :
    ((∀ t, (t.order : ℕ) < n → transform S a f t = transform S a g t) ∧
      ∃ t, (t.order : ℕ) = n ∧ transform S a f t ≠ transform S a g t) ↔
      ((∀ t, (t.order : ℕ) < n → f t = g t) ∧
        ∃ t, (t.order : ℕ) = n ∧ f t ≠ g t) :=
  firstDifference_transform_iff S a n f g

end Ring

#check @RKResearch.DiagonalTreeShift.AgreesThrough
#check @RKResearch.DiagonalTreeShift.FirstDifferenceAt
#check @RKResearch.DiagonalTreeShift.expand_eq_atom_add_lower
#check @RKResearch.DiagonalTreeShift.same_correction
#check @RKResearch.DiagonalTreeShift.transform_at_eq_iff
#check @RKResearch.DiagonalTreeShift.agreesThrough_transform_iff
#check @RKResearch.DiagonalTreeShift.firstDifference_transform_iff

#print axioms RKResearch.DiagonalTreeShift.expand_eq_atom_add_lower
#print axioms RKResearch.DiagonalTreeShift.same_correction
#print axioms RKResearch.DiagonalTreeShift.transform_at_eq_iff
#print axioms RKResearch.DiagonalTreeShift.agreesThrough_transform_iff
#print axioms RKResearch.DiagonalTreeShift.firstDifference_transform_iff
