module

public import RKCert.ReviewedNative.ERK10FixedQ29AdicHeadForms

@[expose] public section

namespace RKResearch.Certified.ERK10FixedQ29Adic.Nonlinear
open Packed

set_option maxRecDepth 80000
set_option maxHeartbeats 0

theorem certUU : Form.check denUU digitsUU exprUU repUU = true := by decide +kernel

theorem certVV : Form.check denVV digitsVV exprVV repVV = true := by decide +kernel

theorem certWW : Form.check denWW digitsWW exprWW repWW = true := by decide +kernel

end RKResearch.Certified.ERK10FixedQ29Adic.Nonlinear
