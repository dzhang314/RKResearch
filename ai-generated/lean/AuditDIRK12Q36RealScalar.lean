import RKCert.ReviewedNative.DIRK12Q36RealScalar

open RKResearch.Certified
open RKResearch.Certified.DIRK12Q36Moments
open RKResearch.Certified.DIRK12MidpointRealInterval
open RKResearch.Certified.DIRK12MidpointMomentTransfers (rel3 rel4)
open RKResearch.Certified.DirectedRatBox

set_option autoImplicit false

example {x f : ℝ} (hX : realX x=0) (hF : realF x f=0) :
    rel3 (moments x f 0) (moments x f 1) (moments x f 2) (moments x f 3)=0 ∧
    rel4 (moments x f 0) (moments x f 1) (moments x f 2) (moments x f 3) (moments x f 4)=0 :=
  real_relations hX hF

open scoped Polynomial

example {x f d v : ℝ} (hx : Encloses xBox x) (hf : Encloses fBox f)
    (hex : realX x=0) (hef : realF x f=0)
    (hs : d+v = S (moments x f)) (hp : d*v=P (moments x f))
    (sites : Fin 10 → ℝ) (distinct : Function.Injective sites)
    (hh : Lagrange.nodal Finset.univ sites=supportHull x f d v)
    (q : ℝ[X]) (hq : q.natDegree<12) :
    PaidNodalQuadrature.quadr Finset.univ sites integral q=integral q :=
  real_paid_scalar hx hf hex hef hs hp sites distinct hh q hq

#print axioms RKResearch.Certified.DIRK12Q36Moments.real_relations
#print axioms RKResearch.Certified.DIRK12Q36Moments.real_paid_scalar
