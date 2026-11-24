module
public import RKCert.Dirk15Replay.H6K3J1W0Part000
public import RKCert.Dirk15Replay.H6K3J1W0Part001
public import RKCert.Dirk15Replay.H6K3J1W0Part002

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay.H6K3J1W0
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

def candidate : List Nat := [428, 415, 230, 933, 278, 995, 296, 619, 504, 974, 991, 379, 748, 994, 281, 666, 3, 192, 116, 386, 366, 750, 563, 168, 784, 744, 178, 324, 194, 864, 999]
private def values : Fin 31 → Nat := fun i => (#[428, 218, 826, 848, 45, 787, 735, 911, 337, 119, 930, 397, 80, 812, 438, 222, 784, 962, 452, 24, 153, 411, 93, 922, 130, 468, 468, 125, 33, 479, 581] : Array Nat)[i.val]!

theorem exactReduction : (anchorGramNorm 6 3).map order15Reduce=residuePoly candidate := by
  apply integer_reduction_of_residue_samples _ _ (d:=30)
    (by decide) ((anchorGramNorm_degree 6 (by decide)).trans (by decide)) (by decide) values
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
    · exact At21.checked
    · exact At22.checked
    · exact At23.checked
    · exact At24.checked
    · exact At25.checked
    · exact At26.checked
    · exact At27.checked
    · exact At28.checked
    · exact At29.checked
    · exact At30.checked
  · decide +kernel

end RKCert.FixedPolynomial.FixedReplay.H6K3J1W0
