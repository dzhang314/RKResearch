module
public import RKCert.Dirk15Replay.Axes
public import RKCert.Dirk15Replay.G5K3J1W0

@[expose] public section
namespace RKCert.FixedPolynomial.FixedReplay.T5K3J1W0
open Polynomial RKCert.Compound RKCert.LU
set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

namespace At120
private def m : Array Nat := #[422212465065984068, 433274431650712851050, 443673622618579933964976, 454321790677192660061176624, 465225513654485615416567448340, 476390925982193906320012433183288, 1046477718126469201152558286561281, 681956288696262821185681629381632, 1257386366672518845184532305412096, 1172092770655751613321488585719808, 802422829944469211148512640630784]
private def l : Array Nat := #[1, 1775, 1818263, 1861901324, 1906586956025, 1952345042970558, 1545463661544274380, 1249001312519675392000, 2179642893032345930039296, 2104081312645376905616293888, 2402531078584721635330773483520]
private def u : Array Nat := #[422212465065984068, 433146079061332791296, 443542637675217676140544, 454187661447797261614448640, 465088165323581349707397464064, 476250281291347398927766991667200, 617208237616580714552584885501952, 339452587559946581258410190176256, 204474700486475898953899240849408, 443992146849858777113670499434496, 164794578029669822194571416698880]
private def swaps : List (Fin 11×Fin 11) := []
private theorem evaluated : (rowMatrix 1009 11 m).det=(797:ZMod 1009) :=
  det_packed_compact 1009 m l u swaps 797 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
private def coefficients : Array Nat := #[68, 618, 688, 816, 788, 568]
private def remainder : Array Nat := #[375, 825, 537, 991, 924, 633]
theorem checked : (parameterGramNorm 5 3 1 0).eval₂ order15Reduce (120:ZMod 1009)=(797:ZMod 1009) := by
  have vv : anchorLead 5^(120:Nat)*(-1:ZMod 1009)^((5+1)*(120-5))*797=(797:ZMod 1009) := by decide +kernel
  exact (parameterGramNorm_eval_ready (n:=5) (k:=3) (j:=1) (w:=0)
    (by decide) (by decide) (by decide) FixedReplay.G5K3J1W0.candidate FixedReplay.G5K3J1W0.exactReduction 120
    (by decide +kernel) m coefficients remainder 797
    (by decide +kernel) (by decide +kernel)
    (packedRowsCheck_sound (by decide +kernel)) evaluated).trans vv
end At120

end RKCert.FixedPolynomial.FixedReplay.T5K3J1W0
