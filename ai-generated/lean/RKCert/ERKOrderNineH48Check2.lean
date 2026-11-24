module
public import RKCert.ERKOrderNineH48Stages
@[expose] public section
namespace RKCert.GoodPrimeDense
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem h48_check2 : norm exactTower.atH 3 exactTower.relU h48Stage1 = h48Stage2 := by decide +kernel
end RKCert.GoodPrimeDense
