module

public import RKCert.ReviewedNative.ERK19LocalFour
public import RKCert.ReviewedNative.ERK19LocalFiveProducer

@[expose] public section

/-! Source-only client: this is the nonzero first-seed branch, not the
uniform ordered stage-30 bound (the zero-first-seed branch is separate). -/
namespace RKResearch.Certified.ERK19
open RKResearch Graded Graded.Reverse Graded.Reverse.LocalLinear

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A : Matrix (Fin 29) (Fin 29) K} {b : Fin 29→K}

theorem width29_nonzero_first_seed_impossible (ha : ∀ i j,i≤j→A i j=0)
    (ho : HasOrder 19 A b) (nz : firstSeed A b≠0) : False := by
  obtain ⟨r,U,τ,F,full,_,_,rank⟩ := width29_nonzero_small_hidden_rank_five ha ho nz
  obtain ⟨h,P,Q,G⟩ := width29_local_five_geometry ha ho nz F full rank
  obtain ⟨e,W,C⟩ := width29_local_five_cover_premises ha ho nz F full rank G
  exact width29_local_five_impossible_of_saturation ha ho F G C

end RKResearch.Certified.ERK19
