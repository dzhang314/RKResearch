module
public import RKCert.Dirk15Replay.Axes

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay.A6K1J1W0
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace At0
private def m : Array Nat := #[516508834063867446066, 534955578137577835287, 1095275429377363172352, 340111844738170093568, 279007904364698271744, 1006269407854665400320, 337543666171511832576]
private def l : Array Nat := #[1, 1527, 1563648, 1601175552, 1639603765248, 1678954255613952, 1719249157748686848]
private def u : Array Nat := #[516508834063867446066, 146421031085070403584, 733258076930812411904, 276701161983964086272, 694059645173833400320, 884058858652642050048, 498062089990157893632]
private def swaps : List (Fin 7×Fin 7) := []
private theorem evaluated : (rowMatrix 1009 7 m).det=(847:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 847 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[937, 502, 532, 367, 862, 4, 862, 42]
theorem checked : (anchorMomentNorm 6 1 1).eval₂ order15Reduce (0:ZMod 1009)=(847:ZMod 1009) :=
  anchorMomentNorm_eval_sparse axes7K1 1 0 m coefficients 847
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At0

namespace At1
private def m : Array Nat := #[631800984524552143666, 911960910144016796439, 280159925620322360320, 614507162834599673856, 483075010680110186496, 364092129788651634688, 939368691576285954048]
private def l : Array Nat := #[1, 1527, 1563648, 1601175552, 1639603765248, 1678954255613952, 1719249157748686848]
private def u : Array Nat := #[631800984524552143666, 696364588782536411136, 161409010645816311808, 856620678801208115200, 23059329492648460288, 398678905213159473152, 953466084309862449152]
private def swaps : List (Fin 7×Fin 7) := []
private theorem evaluated : (rowMatrix 1009 7 m).det=(825:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 825 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[993, 1008, 15, 581, 275, 580, 670, 42]
theorem checked : (anchorMomentNorm 6 1 1).eval₂ order15Reduce (1:ZMod 1009)=(825:ZMod 1009) :=
  anchorMomentNorm_eval_sparse axes7K1 1 1 m coefficients 825
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At1

end RKCert.FixedPolynomial.FixedReplay.A6K1J1W0
