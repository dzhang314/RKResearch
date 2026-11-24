module
public import RKCert.Dirk15Replay.T5K1J1W0Part000
public import RKCert.Dirk15Replay.T5K1J1W0Part001

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay.T5K1J1W0
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

def candidate : List Nat := [429, 659, 751, 68, 640, 179, 3, 640, 503, 320, 544, 545, 637, 711, 536, 467, 410, 501, 287, 1003, 706]
private def values : Fin 21 → Nat := fun i => (#[429, 449, 279, 155, 715, 123, 295, 520, 478, 793, 308, 337, 584, 562, 327, 107, 901, 17, 1001, 61, 81] : Array Nat)[i.val]!

theorem exactReduction : (parameterGramNorm 5 1 1 0).map order15Reduce=residuePoly candidate := by
  apply integer_reduction_of_residue_samples _ _ (d:=20)
    (by decide) ((parameterGramNorm_degree 5 1 1 0).trans (by decide)) (by decide) values
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

end RKCert.FixedPolynomial.FixedReplay.T5K1J1W0
