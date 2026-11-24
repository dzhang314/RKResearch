module
public import RKCert.Dirk15Replay.H5K3J1W0Part000
public import RKCert.Dirk15Replay.H5K3J1W0Part001

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay.H5K3J1W0
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

def candidate : List Nat := [37, 445, 363, 384, 430, 712, 1007, 766, 431, 57, 981, 281, 56, 129, 224, 402, 357, 143, 719, 551, 817]
private def values : Fin 21 → Nat := fun i => (#[37, 211, 485, 496, 581, 534, 879, 576, 151, 12, 913, 914, 586, 22, 517, 688, 269, 384, 530, 774, 900] : Array Nat)[i.val]!

theorem exactReduction : (anchorGramNorm 5 3).map order15Reduce=residuePoly candidate := by
  apply integer_reduction_of_residue_samples _ _ (d:=20)
    (by decide) ((anchorGramNorm_degree 5 (by decide)).trans (by decide)) (by decide) values
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

end RKCert.FixedPolynomial.FixedReplay.H5K3J1W0
