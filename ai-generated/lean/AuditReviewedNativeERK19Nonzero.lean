import RKCert.ReviewedNative.ERK19LocalNonzeroClose

open RKResearch Module
open RKResearch.Certified.Graded
open RKResearch.Certified.Graded.Reverse
open RKResearch.Certified.Graded.PhysicalCensus

-- The exact intended public statement, not a stage-30 claim.
example {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {A : Matrix (Fin 29) (Fin 29) K} {b : Fin 29→K}
    (ha : ∀ i j,i≤j→A i j=0)
    (ho : RKResearch.HasOrder 19 A b) (nz : firstSeed A b≠0) : False :=
  RKResearch.Certified.ERK19.width29_nonzero_first_seed_impossible ha ho nz

-- The coverage interface itself depends on no ordering of either K or labels.
example {K α : Type*} [Field K] {s : ℕ} {label : Fin s→α} {S T R : Set α}
    {V W Z M : Submodule K (Fin s→K)}
    (hV : OnLabels label S V) (hW : OnLabels label T W) (hZ : OnLabels label R Z)
    (st : Disjoint S T) (sr : Disjoint S R) (tr : Disjoint T R)
    (sum : V⊔W⊔Z≤M) (rank : finrank K M≤finrank K V+finrank K W+finrank K Z)
    (b : ∀ i,(labelIndicator label (label i) : Fin s→K)∈M) :
    ∀ i,label i∈S ∨ label i∈T ∨ label i∈R :=
  cover_of_supported_rank_equality hV hW hZ st sr tr sum rank b

#print axioms RKResearch.Certified.Graded.PhysicalCensus.finrank_supported_triple
#print axioms RKResearch.Certified.Graded.PhysicalCensus.cover_of_supported_rank_equality
#print axioms RKResearch.Certified.Graded.Reverse.LocalLinear.local_linear_compensated_contrast
#print axioms RKResearch.Certified.Graded.Reverse.LocalLinear.reflected_clockMass_zero_of_paid_band
#print axioms RKResearch.Certified.Graded.Reverse.LocalLinear.JointBandCensus.cancelled_rank
#print axioms RKResearch.Certified.Graded.Reverse.LocalLinear.JointBandCensus.physical_cover
#print axioms RKResearch.Certified.ERK19.width29_local_hidden_rank_four_impossible
#print axioms RKResearch.Certified.ERK19.width29_local_five_cover_premises
#print axioms RKResearch.Certified.Graded.LocalFivePorts.quintic_eq_zero_of_four_paid_tests
#print axioms RKResearch.Certified.ERK19.width29_nonzero_first_seed_impossible
