module
public import RKCert.Dirk15Replay.A6K4J1W0Part000
public import RKCert.Dirk15Replay.A6K4J1W0Part001

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay.A6K4J1W0
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

def candidate : List Nat := [67, 498, 99, 640, 255, 639, 524, 191, 118, 989, 1001, 424, 374, 554, 380, 843, 415, 550, 643, 683, 797]
private def values : Fin 21 → Nat := fun i => (#[67, 594, 19, 557, 272, 392, 176, 870, 679, 8, 499, 987, 356, 561, 602, 749, 345, 946, 157, 618, 130] : Array Nat)[i.val]!

theorem exactReduction : (anchorMomentNorm 6 4 1).map order15Reduce=residuePoly candidate := by
  apply integer_reduction_of_residue_samples _ _ (d:=20)
    (by decide) ((anchorMomentNorm_degree 6 (by decide) 1).trans (by decide)) (by decide) values
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

end RKCert.FixedPolynomial.FixedReplay.A6K4J1W0
