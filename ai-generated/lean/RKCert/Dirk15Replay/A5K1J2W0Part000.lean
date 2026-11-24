module
public import RKCert.Dirk15Replay.Axes

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay.A5K1J2W0
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace At0
private def m : Array Nat := #[453737662457577581, 245446179691803839, 984036518694943744, 557320571125235712, 132976240859545600, 254663385667338240]
private def l : Array Nat := #[1, 1359, 1391616, 1425014784, 1459215138816, 1494236302147584]
private def u : Array Nat := #[453737662457577581, 471752060967171072, 855683929314689024, 183521801853206528, 1135026952864792576, 631629847738712064]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(252:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 252 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[56, 506, 492, 214, 422, 576, 817]
theorem checked : (anchorMomentNorm 5 1 2).eval₂ order15Reduce (0:ZMod 1009)=(252:ZMod 1009) :=
  anchorMomentNorm_eval_sparse axes6K1 2 0 m coefficients 252
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At0

namespace At1
private def m : Array Nat := #[397442667115446381, 235313080530220223, 1044835113664445440, 405324083701481472, 868188880027779072, 869404734803410944]
private def l : Array Nat := #[1, 1359, 1391616, 1425014784, 1459215138816, 1494236302147584]
private def u : Array Nat := #[397442667115446381, 7881299348009984, 676665844126711808, 928867540183023616, 970645566465769472, 648518346341351424]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(685:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 685 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[14, 337, 497, 706, 688, 66, 817]
theorem checked : (anchorMomentNorm 5 1 2).eval₂ order15Reduce (1:ZMod 1009)=(685:ZMod 1009) :=
  anchorMomentNorm_eval_sparse axes6K1 2 1 m coefficients 685
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At1

end RKCert.FixedPolynomial.FixedReplay.A5K1J2W0
