module
public import RKCert.ERKOrderNineH48Stages
@[expose] public section
namespace RKCert.GoodPrimeDense
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem h48_check3 : norm exactTower.ops 4 exactTower.relH h48Stage2 = h48ExpectedCoeffs := by decide +kernel
end RKCert.GoodPrimeDense
