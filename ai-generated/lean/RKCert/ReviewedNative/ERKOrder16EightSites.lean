module

public import RKCert.ReviewedNative.ERKOrder16ReverseCover
public import RKCert.ReviewedNative.ReverseTerminalHullGain

@[expose] public section

/-! # At least eight distinct quadratic seed sites at true width 24 -/
namespace RKResearch.Certified.ERK16

open RKResearch Module
open RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse
open RKCert.Endpoint.WeightedClock

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A : Matrix (Fin 24) (Fin 24) K} {b : Fin 24 → K}

/-- The width-24 zero-first-seed frame and native outgoing Hermite rank
exclude the last seven-site trace case. E6 really has an independent
terminal-coordinate functional because its original terminal unit is
already absent from E7. No all-zero terminal dimension is counted twice. -/
theorem width24_quadratic_eight_sites (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 16 A b) :
    8≤(weightedSites (reflectedClock A) (quadraticSeed A b)).card := by
  let S := weightedSites (reflectedClock A) (quadraticSeed A b)
  have W := width24_quadratic_cover ha ho
  by_contra! small
  change S.card<8 at small
  have lo : 7≤S.card := W.sites
  have seven : S.card=7 := by omega
  have out : coordinate (K:=K) (Fin.last 23)∉treeSpace A 6 :=
    fun h => W.frame.lastOut (treeSpace_mono A (by decide : 6≤7) h)
  have budget := primitiveBack_terminal_hull_budget ha ho W.frame.lastLive W.frame.seedZero
    (j:=6) (u:=7) seven (by decide) (by decide) out
  have f5 := grade_five_surplus_of_reviewed_order ha ho (by decide : 10≤16)
  have step := Submodule.finrank_lt_finrank_of_lt (zeroSpace_strict_of_separation
    ha (coeff_separated ho (q:=6) (by decide)) (j:=5) (by decide) (by decide))
  have e6 := erk_midpoint_tree_rank ha ho (q:=6) (by decide) (by decide)
  change finrank K (zeroSpace A 5)<finrank K (zeroSpace A 6) at step
  change finrank K (treeSpace A 6)+7+4+1≤24 at budget
  omega

end RKResearch.Certified.ERK16
