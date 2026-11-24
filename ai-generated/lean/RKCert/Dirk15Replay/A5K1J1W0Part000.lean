module
public import RKCert.Dirk15Replay.Axes

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay.A5K1J1W0
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace At0
private def m : Array Nat := #[112589990684263218, 368169269538376471, 340021772725017600, 267965056978780160, 200184533352448000, 901589639171670016]
private def l : Array Nat := #[1, 1527, 1563648, 1601175552, 1639603765248, 1678954255613952]
private def u : Array Nat := #[112589990684263218, 537054255564769280, 577586653068001280, 566328531462651904, 481658660733321216, 1053842312804696064]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(472:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 472 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[56, 506, 492, 214, 422, 576, 817]
theorem checked : (anchorMomentNorm 5 1 1).eval₂ order15Reduce (0:ZMod 1009)=(472:ZMod 1009) :=
  anchorMomentNorm_eval_sparse axes6K1 1 0 m coefficients 472
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At0

namespace At1
private def m : Array Nat := #[28147497671066418, 920986123798104855, 431219665179270144, 607986828845252608, 734986989102694400, 687668656871571456]
private def l : Array Nat := #[1, 1527, 1563648, 1601175552, 1639603765248, 1678954255613952]
private def u : Array Nat := #[28147497671066418, 395190867302598656, 455989463128997888, 723954518420619264, 116867090916311040, 292733975779082240]
private def swaps : List (Fin 6×Fin 6) := []
private theorem evaluated : (rowMatrix 1009 6 m).det=(19:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 19 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[14, 337, 497, 706, 688, 66, 817]
theorem checked : (anchorMomentNorm 5 1 1).eval₂ order15Reduce (1:ZMod 1009)=(19:ZMod 1009) :=
  anchorMomentNorm_eval_sparse axes6K1 1 1 m coefficients 19
    (by decide +kernel) (packedRowsCheck_sound (by decide +kernel)) evaluated
end At1

end RKCert.FixedPolynomial.FixedReplay.A5K1J1W0
