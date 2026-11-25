import RKCert.ReviewedNative.ReviewedQuadratureUnboundedCensus

open Polynomial RKCert.Endpoint RKResearch RKResearch.Certified.Graded
open RKResearch.Certified.Graded.EffectiveDonors RKResearch.Certified.Graded.SignedQuadrature
open RKCert.ReviewedNative.UnitBetaSquareMass RKCert.ReviewedNative.UnitAffineSquareMass
open RKCert.ReviewedNative.FormalSignedQuadrature
open scoped Classical

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

example (a b : ℕ) (P : K[X]) (P0 : P ≠ 0) :
    0 < (formalPrimitive (X^a * (1-X)^b * P^2)).eval 1 :=
  beta_square_pos a b P0

example (a b : ℕ) (L : List K[X]) (P : K[X]) (P0 : P ≠ 0)
    (good : ∀ f ∈ L, EndpointAffine f) :
    0 < mass (betaWeight a b * L.prod * P^2) :=
  mass_beta_list_prod_sq_pos L P0 a b good

example {ι : Type*} [Fintype ι] {p : ℕ}
    {A : Matrix ι ι K} {w : ι → K} (ho : HasOrder p A w) :
    let T := activeAggregates (nodes A) w
    let mu := clockMass (nodes A) w
    p+(exteriorSites T).card+2*(negativeInteriorSites T mu).card≤2*Fintype.card ι :=
  order_plus_exterior_and_negative_interior_le_twice_stages ho

#check @RKCert.ReviewedNative.UnitBetaSquareMass.beta_square_pos
#check @RKCert.ReviewedNative.UnitAffineSquareMass.mass_beta_finset_prod_sq_pos
#check @RKCert.ReviewedNative.FormalSignedQuadrature.UnitLaw.exterior_and_negative_budget
#check @RKResearch.Certified.Graded.SignedQuadrature.unit_law
#print axioms RKCert.ReviewedNative.UnitBetaSquareMass.beta_square_pos
#print axioms RKCert.ReviewedNative.UnitAffineSquareMass.mass_beta_list_prod_sq_pos
#print axioms RKCert.ReviewedNative.FormalSignedQuadrature.UnitLaw.exterior_and_negative_budget
#print axioms RKResearch.Certified.Graded.SignedQuadrature.order_plus_exterior_and_negative_interior_le_twice_stages
