module
public import RKCert.ERKOrderNineH48Stages
@[expose] public section
namespace RKCert.GoodPrimeDense
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem h48_check1 : norm exactTower.atU 2 exactTower.relV h48Stage0 = h48Stage1 := by decide +kernel
end RKCert.GoodPrimeDense
