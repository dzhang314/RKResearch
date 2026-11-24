module
public import RKCert.Dirk15Replay.Axes

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay.A6K1J2W0
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace At0
private def m : Array Nat := #[732105155425347829869, 1132168917523923842239, 342417686868348042240, 614507162072687575040, 961536654893962493952, 282588701725244260352, 423337239072919781376]
private def l : Array Nat := #[1, 1359, 1391616, 1425014784, 1459215138816, 1494236302147584, 1530097973399126016]
private def u : Array Nat := #[732105155425347829869, 169479461177206617088, 568390301771289853952, 984594965051285176320, 335500277687359897600, 729922035505979981824, 232890143930583089152]
private def swaps : List (Fin 7×Fin 7) := []
private theorem evaluated : (rowMatrix 1009 7 m).det=(858:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 858 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[937, 502, 532, 367, 862, 4, 862, 42]
theorem checked : (anchorMomentNorm 6 1 2).eval₂ order15Reduce (0:ZMod 1009)=(858:ZMod 1009) :=
  anchorMomentNorm_eval_sparse axes7K1 2 0 m coefficients 858
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At0

namespace At1
private def m : Array Nat := #[33434723633598562413, 220208007379907884223, 186773283746423700480, 21905508704768229376, 1097581392437570437120, 242236449064004616192, 824553922676102529024]
private def l : Array Nat := #[1, 1359, 1391616, 1425014784, 1459215138816, 1494236302147584, 1530097973399126016]
private def u : Array Nat := #[33434723633598562413, 652553571607475500032, 281312847124184956928, 9223372153892634624, 334347356182753050624, 1075798486888034074624, 1095275429376504627200]
private def swaps : List (Fin 7×Fin 7) := []
private theorem evaluated : (rowMatrix 1009 7 m).det=(149:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 149 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[993, 1008, 15, 581, 275, 580, 670, 42]
theorem checked : (anchorMomentNorm 6 1 2).eval₂ order15Reduce (1:ZMod 1009)=(149:ZMod 1009) :=
  anchorMomentNorm_eval_sparse axes7K1 2 1 m coefficients 149
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At1

end RKCert.FixedPolynomial.FixedReplay.A6K1J2W0
