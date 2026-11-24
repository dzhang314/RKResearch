module
public import RKCert.Dirk15Replay.G5K1J1W0Part000
public import RKCert.Dirk15Replay.G5K1J1W0Part001

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay.G5K1J1W0
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

def candidate : List Nat := [675, 897, 1, 506, 103, 315, 245, 888, 716, 90, 234, 765, 396, 429, 276, 557, 861, 436, 375, 169, 56]
private def values : Fin 21 → Nat := fun i => (#[675, 918, 858, 581, 121, 388, 21, 154, 258, 40, 306, 312, 755, 269, 312, 827, 55, 840, 310, 102, 998] : Array Nat)[i.val]!

theorem exactReduction : (nodeGramNorm 5 1 1 0).map order15Reduce=residuePoly candidate := by
  apply integer_reduction_of_residue_samples _ _ (d:=20)
    (by decide) ((nodeGramNorm_degree (by decide) (by decide) 1 0).trans (by decide)) (by decide) values
  · intro i
    rw [eval_map]
    fin_cases i
    · exact At0.checked
    · exact At1.checked
    · exact At2.checked
    · exact At3.checked
    · exact At4.checked
    · exact At5.checked
    · exact At6.checked
    · exact At7.checked
    · exact At8.checked
    · exact At9.checked
    · exact At10.checked
    · exact At11.checked
    · exact At12.checked
    · exact At13.checked
    · exact At14.checked
    · exact At15.checked
    · exact At16.checked
    · exact At17.checked
    · exact At18.checked
    · exact At19.checked
    · exact At20.checked
  · decide +kernel

end RKCert.FixedPolynomial.FixedReplay.G5K1J1W0
