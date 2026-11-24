module
public import RKCert.Dirk15Replay.A6K3J2W0Part000
public import RKCert.Dirk15Replay.A6K3J2W0Part001

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay.A6K3J2W0
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

def candidate : List Nat := [938, 388, 806, 529, 346, 289, 881, 658, 207, 23, 388, 442, 658, 769, 59, 491]
private def values : Fin 16 → Nat := fun i => (#[938, 809, 394, 164, 975, 671, 231, 141, 817, 717, 550, 939, 688, 282, 521, 179] : Array Nat)[i.val]!

theorem exactReduction : (anchorMomentNorm 6 3 2).map order15Reduce=residuePoly candidate := by
  apply integer_reduction_of_residue_samples _ _ (d:=15)
    (by decide) ((anchorMomentNorm_degree 6 (by decide) 2).trans (by decide)) (by decide) values
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

end RKCert.FixedPolynomial.FixedReplay.A6K3J2W0
