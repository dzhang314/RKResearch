import RKCert.ReviewedNative.RationalVandermondeMoments

open RKResearch.Certified.RationalMoments
open scoped BigOperators

section

variable {n : ℕ}

example (z : Fin n → ℚ) (inj : Function.Injective z) (m : Fin n → ℚ) (k : Fin n) :
    (∑ i, momentSolve z m i * z i ^ k.val) = m k :=
  momentSolve_spec inj m k

example (z : Fin n → ℚ) (inj : Function.Injective z) (x : ℚ) (k : Fin n) :
    (∑ i, primitiveWeights z x i * z i ^ k.val) =
      x ^ (k.val + 1) / ((k.val + 1 : ℕ) : ℚ) :=
  primitiveWeights_spec inj x k

example (lam : Fin n → ℚ) (inj : Function.Injective lam) (β a : ℚ) (k : Fin n) :
    (∑ l, terminalCopyWeights lam β a l * lam l ^ k.val) =
      if k.val = 0 then β else if k.val = 1 then a else 0 :=
  terminalCopyWeights_spec inj β a k

end

#print axioms RKResearch.Certified.RationalMoments.momentSolve_spec
#print axioms RKResearch.Certified.RationalMoments.primitiveWeights_spec
#print axioms RKResearch.Certified.RationalMoments.terminalCopyWeights_spec
