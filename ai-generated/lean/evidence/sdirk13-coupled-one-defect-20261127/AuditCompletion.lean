import RKCert.ReviewedNative.OneDefectCompletion

open RKResearch.Certified.OneDefectCompletion
open scoped Matrix BigOperators

example {K : Type*} [Field K] {ι : Type*} [Fintype ι]
    (l e q z : ι → K) (β a : K) (hz : e ⬝ᵥ q ≠ 0)
    (hp : l ⬝ᵥ q = β*(e ⬝ᵥ q)) :
    l ⬝ᵥ (z + ((a-e ⬝ᵥ z)/(e ⬝ᵥ q)) • q) =
      (l-β • e) ⬝ᵥ z + β*a :=
  complete_feed l e q z β a hz hp

#print axioms complete_feed
#print axioms projection_response
#print axioms last_paid_column
