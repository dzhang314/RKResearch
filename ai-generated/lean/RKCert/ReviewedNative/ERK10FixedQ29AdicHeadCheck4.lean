module

public import RKCert.ReviewedNative.ERK10FixedQ29AdicHeadForms

@[expose] public section

namespace RKResearch.Certified.ERK10FixedQ29Adic.Nonlinear
open Packed

set_option maxRecDepth 80000
set_option maxHeartbeats 0

theorem certS : Form.check denS digitsS exprS repZero = true := by decide +kernel

theorem certQ : Form.check denQ digitsQ exprQ repZero = true := by decide +kernel

end RKResearch.Certified.ERK10FixedQ29Adic.Nonlinear
