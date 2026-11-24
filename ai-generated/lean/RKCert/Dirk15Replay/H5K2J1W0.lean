module
public import RKCert.Dirk15Replay.H5K2J1W0Part000

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay.H5K2J1W0
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

def candidate : List Nat := [27, 142, 943, 832, 0, 585, 622, 387, 521, 281, 337]
private def values : Fin 11 → Nat := fun i => (#[27, 641, 533, 624, 317, 476, 209, 620, 941, 235, 902] : Array Nat)[i.val]!

theorem exactReduction : (anchorGramNorm 5 2).map order15Reduce=residuePoly candidate := by
  apply integer_reduction_of_residue_samples _ _ (d:=10)
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
  · decide +kernel

end RKCert.FixedPolynomial.FixedReplay.H5K2J1W0
