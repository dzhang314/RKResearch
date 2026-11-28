module

public import RKCert.ReviewedNative.ERK10FixedQ29AdicPhaseForms

@[expose] public section

namespace RKResearch.Certified.ERK10FixedQ29Adic.Nonlinear
open Packed

set_option maxRecDepth 80000
set_option maxHeartbeats 0

theorem certD0 : Form.check denD0 digitsD0 (exprD 0) (repD 0) = true := by decide +kernel

theorem certD1 : Form.check denD1 digitsD1 (exprD 1) (repD 1) = true := by decide +kernel

theorem certD2 : Form.check denD2 digitsD2 (exprD 2) (repD 2) = true := by decide +kernel

theorem certD3 : Form.check denD3 digitsD3 (exprD 3) (repD 3) = true := by decide +kernel

theorem certD4 : Form.check denD4 digitsD4 (exprD 4) (repD 4) = true := by decide +kernel

theorem certD5 : Form.check denD5 digitsD5 (exprD 5) (repD 5) = true := by decide +kernel

theorem certD6 : Form.check denD6 digitsD6 (exprD 6) (repD 6) = true := by decide +kernel

theorem certD7 : Form.check denD7 digitsD7 (exprD 7) (repD 7) = true := by decide +kernel

end RKResearch.Certified.ERK10FixedQ29Adic.Nonlinear
