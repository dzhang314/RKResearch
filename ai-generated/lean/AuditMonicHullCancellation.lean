module

import RKCert.ReviewedNative.MonicHullCancellation

open RKResearch.ContextCompletion.MonicHull
open Polynomial
open scoped Polynomial

/- Below the cutoff no moment law is required. -/
example {K : Type*} [Field K] {F H : K[X]} (monic : H.Monic)
    (below : F.natDegree < H.natDegree) : F %ₘ H = F :=
  modByMonic_eq_self_of_natDegree_lt monic below

/- At the exact cutoff the actual discarded polynomial is on the hull line. -/
example {K : Type*} [Field K] {F H : K[X]} (monic : H.Monic)
    (sat : F.natDegree = H.natDegree) :
    F - F %ₘ H = ((F /ₘ H).coeff 0) • H :=
  sub_modByMonic_eq_smul_of_natDegree_le monic sat.le

/- The moment endpoint retains the arbitrary module codomain. -/
example {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {F H : K[X]}
    (m : K[X] →ₗ[K] V) (monic : H.Monic) (bound : F.natDegree ≤ H.natDegree)
    (kills : m H = 0) : m (F %ₘ H) = m F :=
  linearMoment_modByMonic_eq_of_natDegree_le m monic bound kills

#print axioms RKResearch.ContextCompletion.MonicHull.modByMonic_eq_self_of_natDegree_lt
#print axioms RKResearch.ContextCompletion.MonicHull.sub_modByMonic_eq_smul_of_natDegree_le
#print axioms RKResearch.ContextCompletion.MonicHull.linearMoment_modByMonic_eq_of_natDegree_le
