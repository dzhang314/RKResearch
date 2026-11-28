module

public import RKCert.ReviewedNative.ERK10FixedQ29AdicRemainderForms

@[expose] public section

namespace RKResearch.Certified.ERK10FixedQ29Adic.Nonlinear
open Packed

set_option maxRecDepth 80000
set_option maxHeartbeats 0

theorem certRem6 : Form.check denRemainder digitsRemainder (exprRemainder 6) repZero = true := by decide +kernel

theorem certRem7 : Form.check denRemainder digitsRemainder (exprRemainder 7) repZero = true := by decide +kernel

theorem certRem8 : Form.check denRemainder digitsRemainder (exprRemainder 8) repZero = true := by decide +kernel

end RKResearch.Certified.ERK10FixedQ29Adic.Nonlinear
