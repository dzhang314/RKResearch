module

public import RKCert.ReviewedNative.ERK10FixedQ29AdicPhaseForms

@[expose] public section

namespace RKResearch.Certified.ERK10FixedQ29Adic.Nonlinear
open Packed

set_option maxRecDepth 80000
set_option maxHeartbeats 0

theorem certM0 : Form.check denM0 digitsM0 (exprM 0) (repM 0) = true := by decide +kernel

theorem certM1 : Form.check denM1 digitsM1 (exprM 1) (repM 1) = true := by decide +kernel

theorem certM2 : Form.check denM2 digitsM2 (exprM 2) (repM 2) = true := by decide +kernel

theorem certM3 : Form.check denM3 digitsM3 (exprM 3) (repM 3) = true := by decide +kernel

theorem certM4 : Form.check denM4 digitsM4 (exprM 4) (repM 4) = true := by decide +kernel

theorem certM5 : Form.check denM5 digitsM5 (exprM 5) (repM 5) = true := by decide +kernel

theorem certM6 : Form.check denM6 digitsM6 (exprM 6) (repM 6) = true := by decide +kernel

end RKResearch.Certified.ERK10FixedQ29Adic.Nonlinear
