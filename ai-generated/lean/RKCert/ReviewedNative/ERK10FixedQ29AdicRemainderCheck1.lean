module

public import RKCert.ReviewedNative.ERK10FixedQ29AdicRemainderForms

@[expose] public section

namespace RKResearch.Certified.ERK10FixedQ29Adic.Nonlinear
open Packed

set_option maxRecDepth 80000
set_option maxHeartbeats 0

theorem certRem3 : Form.check denRemainder digitsRemainder (exprRemainder 3) repZero = true := by decide +kernel

theorem certRem4 : Form.check denRemainder digitsRemainder (exprRemainder 4) repZero = true := by decide +kernel

theorem certRem5 : Form.check denRemainder digitsRemainder (exprRemainder 5) repZero = true := by decide +kernel

end RKResearch.Certified.ERK10FixedQ29Adic.Nonlinear
