module

public import RKCert.ReviewedNative.ERK18ReverseCarrier
import Lean.Elab.Tactic.Omega

public section

namespace RKResearch.Certified.Graded.Reverse

open RKResearch Module RKCert.Endpoint.WeightedClock RKCert.OneEscape
open scoped Matrix

variable {K : Type*} [Field K] [CharZero K] {s p : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}

example (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder p A b)
    (n : ℕ) (pay : n+3≤p)
    (inv : (primitiveBack A b (n+1)).map (diag (reflectedClock A)) ≤ primitiveBack A b (n+1)) :
    finrank K (primitiveBack A b n) + (n+2)/2 ≤ finrank K (primitiveBack A b (n+1)) :=
  primitiveBack_clock_invariant_incoming ha ho n pay inv

example (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder p A b)
    (pay : 10≤p) (first : firstSeed A b=0)
    (one : (weightedSites (reflectedClock A) (quadraticSeed A b)).card≤1) :
    5≤finrank K (primitiveBack A b 4) :=
  primitiveBack_rank_four_of_one_clock ha ho pay first one

example (n : ℕ)
    (rank : finrank K (primitiveBack A b (n+1))≤finrank K (primitiveBack A b n)+1)
    (out : ¬(primitiveBack A b n).map (diag (reflectedClock A))≤primitiveBack A b n) :
    primitiveBack A b (n+1) =
      primitiveBack A b n ⊔ (primitiveBack A b n).map (diag (reflectedClock A)) :=
  primitiveBack_clock_step_of_unit_rank n rank out

example (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 18 A b)
    {t : Fin s} (last : LastActive b t) (first : firstSeed A b=0)
    (one : (weightedSites (reflectedClock A) (quadraticSeed A b)).card=1)
    (room : finrank K (zeroAt (annih (treeSpace A 8)) t)≤9) :
    ∃ (r : ℕ) (U : Submodule K (Fin s → K)) (w : Fin s → K),
      reflectedClock A t=0 ∧ (∀ n, primitiveBack A b n ≤ tailZero t) ∧
      primitiveBack A b 8=zeroAt (annih (treeSpace A 8)) t ∧
      (∀ n, 4≤n → n≤8 → finrank K (primitiveBack A b n)=n+1) ∧
      (∀ k, k≤4 → primitiveBack A b (4+k)=chain (diag (reflectedClock A)) U w (r+k)) ∧
      U.map (diag (reflectedClock A))≤U ∧ finrank K U+r=5 ∧
      1≤finrank K U ∧ finrank K U≤3 ∧
      r+4<(HeadFiber.escapeSites (reflectedClock A) w U).card := by
  obtain ⟨r,U,w,carrier⟩ := rank_nine_reverse_carrier_of_measured_room ha ho last first one room
  exact ⟨r,U,w,carrier.reflectedZero,carrier.tail,carrier.full,carrier.ranks,
    carrier.chains,carrier.stable,carrier.rankSplit,carrier.corePos,carrier.coreCap,
    carrier.escapeSites⟩

-- Exactly the seven actual powers used in the separate dimension-two analysis.
example {t : Fin s} {r : ℕ} {U : Submodule K (Fin s → K)} {w : Fin s → K}
    (carrier : RankNineReverseCarrier A b t r U w) (two : finrank K U=2) :
    primitiveBack A b 8=chain (diag (reflectedClock A)) U w 7 := by
  have split := carrier.rankSplit
  have r3 : r=3 := by omega
  simpa only [r3] using carrier.chains 4 (by decide)

#print axioms primitiveBack_clock_invariant_incoming
#print axioms primitiveBack_rank_four_of_one_clock
#print axioms primitiveBack_clock_step_of_unit_rank
#print axioms rank_nine_reverse_carrier_of_measured_room

end RKResearch.Certified.Graded.Reverse
