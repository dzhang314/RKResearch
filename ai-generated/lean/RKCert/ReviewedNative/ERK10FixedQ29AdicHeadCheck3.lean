module

public import RKCert.ReviewedNative.ERK10FixedQ29AdicHeadForms

@[expose] public section

namespace RKResearch.Certified.ERK10FixedQ29Adic.Nonlinear
open Packed

set_option maxRecDepth 80000
set_option maxHeartbeats 0

theorem certU : Form.check denU digitsU exprU repU = true := by decide +kernel

theorem certV : Form.check denV digitsV exprV repV = true := by decide +kernel

theorem certW : Form.check denW digitsW exprW repW = true := by decide +kernel

theorem certDet : Form.check denDet digitsDet exprDet repDet = true := by decide +kernel

end RKResearch.Certified.ERK10FixedQ29Adic.Nonlinear
