module

import RKCert.ReviewedNative.CanonicalSplitUniqueness

/-! Typed clients for the literal split-tableau result only. -/
open RKResearch RKResearch.CanonicalUniqueness RKResearch.CanonicalVisibility
open RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse
open scoped Classical Matrix

section
variable {ι κ K : Type*} [Fintype ι] [Fintype κ] [Field K]
variable {A : Matrix ι ι K} {B : Matrix κ κ K} {b : ι → K} {d : κ → K}

example (same : ∀ t : FiniteRootedTree, b ⬝ᵥ Φ t A = d ⬝ᵥ Φ t B)
    (fullA : treeSpan A = ⊤) (fullB : treeSpan B = ⊤)
    (obsA : invisible A b = ⊥) (obsB : invisible B d = ⊥) :
    ∃ e : κ ≃ ι, (∀ j k, B j k = A (e j) (e k)) ∧ ∀ j, d j = b (e j) :=
  permutation_of_same_series A B b d same fullA fullB obsA obsB

example (C : TreeWord) (t : FiniteRootedTree) :
    (C.context A).eval A (Φ t A) = Φ (C.insert t) A :=
  TreeWord.eval_tree A C t

example (same : ∀ t : FiniteRootedTree, b ⬝ᵥ Φ t A = d ⬝ᵥ Φ t B)
    (C : TreeWord) (t : FiniteRootedTree) :
    row b ((C.context A).eval A (Φ t A)) = row d ((C.context B).eval B (Φ t B)) :=
  same_treeWord A B b d same C t

example (same : ∀ t : FiniteRootedTree, b ⬝ᵥ Φ t A = d ⬝ᵥ Φ t B)
    (x : ι → K) (y : κ → K) (h : (x,y) ∈ pairedSpan A B) : row b x = row d y :=
  pair_readout A B b d same h

end

#check @RKResearch.CanonicalUniqueness.permutation_of_same_series
#check @RKResearch.CanonicalUniqueness.TreeWord.eval_tree
#check @RKResearch.CanonicalUniqueness.same_treeWord
#check @RKResearch.CanonicalUniqueness.pair_readout
#check @RKResearch.CanonicalUniqueness.TreeWord.insert
#check @RKResearch.CanonicalUniqueness.TreeWord.context
#check @RKResearch.CanonicalUniqueness.treeSpan
#check @RKResearch.CanonicalUniqueness.pairedSpan

#print axioms RKResearch.CanonicalUniqueness.permutation_of_same_series
#print axioms RKResearch.CanonicalUniqueness.TreeWord.eval_tree
#print axioms RKResearch.CanonicalUniqueness.same_treeWord
#print axioms RKResearch.CanonicalUniqueness.pair_readout
