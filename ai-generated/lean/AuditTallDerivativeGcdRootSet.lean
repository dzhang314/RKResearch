module

public import RKCert.ReviewedNative.TallDerivativeGcdRootSet

@[expose] public section

open Polynomial RKResearch.Certified.TallFiniteResponse
open scoped Polynomial

variable {K L : Type*} [Field K] [Field L] (Q : K[X])

example (φ : K →+* L) :
    derivativeGcdQuotientDegree (Q.map φ) = derivativeGcdQuotientDegree Q :=
  derivativeGcdQuotientDegree_map Q φ

example [Algebra K L] [CharZero L] (hQ : Q ≠ 0)
    (hs : (Q.map (algebraMap K L)).Splits) :
    derivativeGcdQuotientDegree Q = (Q.rootSet L).ncard :=
  derivativeGcdQuotientDegree_eq_ncard_rootSet_of_splits Q hQ hs

#print axioms derivativeGcdQuotientDegree_map
#print axioms derivativeGcdQuotientDegree_eq_card_toFinset_of_splits
#print axioms derivativeGcdQuotientDegree_eq_ncard_rootSet_of_splits
