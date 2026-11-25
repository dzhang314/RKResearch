module

import RKCert.ReviewedNative.DiagonalTreeShiftMatrix

/-! Typed clients of the checked free literal-tree shift and matrix evaluation.
The strict-order consumer is not imported. -/
open RKResearch RKResearch.DiagonalTreeShift
open scoped FiniteRootedTree Matrix

section Core

variable (R : Type*) [CommSemiring R]

example (t u v : FiniteRootedTree) :
    join R (join R (atom R t) (atom R u)) (atom R v) =
      atom R (t # (u # v)) := by
  rw [join_assoc, join_atom, join_atom]

example {V : Type*} [AddCommMonoid V] [Module R V]
    (a b : R) (f : FiniteRootedTree → V) :
    (operator R a).comp (operator R b) = operator R (a + b) ∧
      transform R a (transform R b f) = transform R (a + b) f :=
  ⟨operator_comp R a b, transform_comp R a b f⟩

end Core

section Inverse

variable (S : Type*) [CommRing S]
variable {V : Type*} [AddCommMonoid V] [Module S V]

example (a : S) (f : FiniteRootedTree → V) :
    transform S (-a) (transform S a f) = f ∧
      transform S a (transform S (-a) f) = f :=
  ⟨transform_neg_left S a f, transform_neg_right S a f⟩

end Inverse

section Matrix

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommSemiring R]

example (A : Matrix ι ι R) (a : R) (t : FiniteRootedTree) :
    stageLift A (expand R a t) = Φ t (A + a • (1 : Matrix ι ι R)) :=
  stageLift_expand A a t

example (A : Matrix ι ι R) (b : ι → R) (a : R) (t : FiniteRootedTree) :
    transform R a (fun u => b ⬝ᵥ Φ u A) t =
      b ⬝ᵥ Φ t (A + a • (1 : Matrix ι ι R)) :=
  transform_tableau_output A b a t

example (A : Matrix ι ι R) (b : ι → R) (a : R) :
    b ⬝ᵥ Φ (.leaf ◂ .leaf) (A + a • (1 : Matrix ι ι R)) =
      (b ⬝ᵥ Φ (.leaf ◂ .leaf) A) + a • (b ⬝ᵥ Φ .leaf A) := by
  rw [← transform_tableau_output A b a (.leaf ◂ .leaf), transform_first_edge]

end Matrix

#check @RKResearch.DiagonalTreeShift.join_assoc
#check @RKResearch.DiagonalTreeShift.expand_rootedSum
#check @RKResearch.DiagonalTreeShift.operator_comp
#check @RKResearch.DiagonalTreeShift.transform_first_edge
#check @RKResearch.DiagonalTreeShift.transform_comp
#check @RKResearch.DiagonalTreeShift.transform_neg_left
#check @RKResearch.DiagonalTreeShift.transform_neg_right
#check @RKResearch.DiagonalTreeShift.stageLift_expand
#check @RKResearch.DiagonalTreeShift.transform_tableau_output

#print axioms RKResearch.DiagonalTreeShift.join_assoc
#print axioms RKResearch.DiagonalTreeShift.expand_rootedSum
#print axioms RKResearch.DiagonalTreeShift.operator_comp
#print axioms RKResearch.DiagonalTreeShift.transform_first_edge
#print axioms RKResearch.DiagonalTreeShift.transform_comp
#print axioms RKResearch.DiagonalTreeShift.transform_neg_left
#print axioms RKResearch.DiagonalTreeShift.transform_neg_right
#print axioms RKResearch.DiagonalTreeShift.stageLift_expand
#print axioms RKResearch.DiagonalTreeShift.transform_tableau_output
