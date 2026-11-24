module
public import RKCert.Dirk15Replay.A6K3J1W0Part000
public import RKCert.Dirk15Replay.A6K3J1W0Part001

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay.A6K3J1W0
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

def candidate : List Nat := [407, 415, 745, 173, 917, 144, 135, 338, 669, 689, 597, 29, 928, 107, 806, 294]
private def values : Fin 16 → Nat := fun i => (#[407, 330, 686, 498, 684, 831, 278, 634, 48, 918, 55, 215, 240, 4, 64, 81] : Array Nat)[i.val]!

theorem exactReduction : (anchorMomentNorm 6 3 1).map order15Reduce=residuePoly candidate := by
  apply integer_reduction_of_residue_samples _ _ (d:=15)
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
  · decide +kernel

end RKCert.FixedPolynomial.FixedReplay.A6K3J1W0
