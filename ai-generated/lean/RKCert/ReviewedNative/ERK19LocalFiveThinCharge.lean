module

public import RKCert.ReviewedNative.ERK19LocalFiveGeometry
public import RKCert.ReviewedNative.LocalLinearMinimalCharge

@[expose] public section
/-! Draft width-29 application of the neutral minimal-site reverse charge. -/

namespace RKResearch.Certified.ERK19
open RKResearch Module Polynomial Graded Graded.Reverse Graded.Reverse.LocalLinear
open RKCert.Endpoint.WeightedClock
open scoped Classical
noncomputable section

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A : Matrix (Fin 29) (Fin 29) K} {b : Fin 29→K}
variable {r : ℕ} {U : Submodule K (Fin 29→K)} {τ h : Fin 29→K} {P Q : K[X]}

/-- The small-support census only has to show n+r=10; no actual reverse
flag equality at L_9 is added. -/
theorem width29_local_five_minimal_reverse_sites_impossible
    (ha : ∀ i j,i≤j→A i j=0) (ho : HasOrder 19 A b) (nz : firstSeed A b≠0)
    (F : LocalLinearBand A b 8 r U τ) (G : LocalFiveGeometry A b r U τ h P Q)
    (minimum : r+(weightedSites (reflectedClock A) τ).card=10) : False := by
  have rb : 1≤r ∧ r≤2 := by rcases F.coreRank with z|z <;> omega
  have H := (ordered_width29_frame ha ho).1
  obtain ⟨d,e⟩ := H.reverse.flagExact (r-1) (by omega)
  have ru : finrank K U=r := by rw [F.core,←e,d,first_dim_one nz]; omega
  have g := local_linear_minimal_sites_paid_gain ha ho F ru minimum (by decide) 4 (by decide)
  have cap := G.reverseCap
  change 14≤finrank K (primitiveBack A b 10) at g
  omega

end
end RKResearch.Certified.ERK19
