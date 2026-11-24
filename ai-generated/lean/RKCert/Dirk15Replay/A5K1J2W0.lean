module
public import RKCert.Dirk15Replay.A5K1J2W0Part000

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay.A5K1J2W0
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

def candidate : List Nat := [252, 433]
private def values : Fin 2 → Nat := fun i => (#[252, 685] : Array Nat)[i.val]!

theorem exactReduction : (anchorMomentNorm 5 1 2).map order15Reduce=residuePoly candidate := by
  apply integer_reduction_of_residue_samples _ _ (d:=1)
    (by decide) ((anchorMomentNorm_degree 5 (by decide) 2).trans (by decide)) (by decide) values
  · intro i
    rw [eval_map]
    fin_cases i
    · exact At0.checked
    · exact At1.checked
  · decide +kernel

end RKCert.FixedPolynomial.FixedReplay.A5K1J2W0
