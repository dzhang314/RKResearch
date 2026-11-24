module
public import RKCert.Dirk15Replay.H6K2J1W0Part000
public import RKCert.Dirk15Replay.H6K2J1W0Part001

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay.H6K2J1W0
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

def candidate : List Nat := [931, 382, 426, 763, 169, 871, 529, 791, 510, 697, 834, 472, 991]
private def values : Fin 13 → Nat := fun i => (#[931, 294, 59, 808, 629, 280, 34, 656, 386, 93, 623, 880, 813] : Array Nat)[i.val]!

theorem exactReduction : (anchorGramNorm 6 2).map order15Reduce=residuePoly candidate := by
  apply integer_reduction_of_residue_samples _ _ (d:=12)
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
  · decide +kernel

end RKCert.FixedPolynomial.FixedReplay.H6K2J1W0
