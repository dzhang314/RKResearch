module

public import RKCert.ReviewedNative.ERK10FixedQ29AdicRemainderForms

@[expose] public section

namespace RKResearch.Certified.ERK10FixedQ29Adic.Nonlinear
open Packed

set_option maxRecDepth 80000
set_option maxHeartbeats 0

theorem certRem0 : Form.check denRemainder digitsRemainder (exprRemainder 0) repZero = true := by decide +kernel

theorem certRem1 : Form.check denRemainder digitsRemainder (exprRemainder 1) repZero = true := by decide +kernel

theorem certRem2 : Form.check denRemainder digitsRemainder (exprRemainder 2) repZero = true := by decide +kernel

end RKResearch.Certified.ERK10FixedQ29Adic.Nonlinear
