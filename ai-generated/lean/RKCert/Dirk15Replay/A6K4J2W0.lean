module
public import RKCert.Dirk15Replay.A6K4J2W0Part000
public import RKCert.Dirk15Replay.A6K4J2W0Part001

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay.A6K4J2W0
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

def candidate : List Nat := [612, 208, 837, 598, 265, 847, 893, 363, 696, 329, 140, 185, 761, 612, 848, 762, 451, 497, 179, 914, 651]
private def values : Fin 21 → Nat := fun i => (#[612, 549, 323, 79, 694, 978, 711, 481, 606, 128, 914, 831, 884, 290, 919, 756, 205, 86, 413, 368, 70] : Array Nat)[i.val]!

theorem exactReduction : (anchorMomentNorm 6 4 2).map order15Reduce=residuePoly candidate := by
  apply integer_reduction_of_residue_samples _ _ (d:=20)
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
    · exact At16.checked
    · exact At17.checked
    · exact At18.checked
    · exact At19.checked
    · exact At20.checked
  · decide +kernel

end RKCert.FixedPolynomial.FixedReplay.A6K4J2W0
