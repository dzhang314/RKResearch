module

public import RKCert.ReviewedNative.ERK10FixedQ29AdicRemainderForms

@[expose] public section

namespace RKResearch.Certified.ERK10FixedQ29Adic.Nonlinear
open Packed

set_option maxRecDepth 80000
set_option maxHeartbeats 0

theorem certRem9 : Form.check denRemainder digitsRemainder (exprRemainder 9) repZero = true := by decide +kernel

theorem certRem10 : Form.check denRemainder digitsRemainder (exprRemainder 10) repZero = true := by decide +kernel

end RKResearch.Certified.ERK10FixedQ29Adic.Nonlinear
