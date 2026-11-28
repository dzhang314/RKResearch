module

public import RKCert.ReviewedNative.ERK10FixedQ29AdicPhaseForms

@[expose] public section

namespace RKResearch.Certified.ERK10FixedQ29Adic.Nonlinear
open Packed

set_option maxRecDepth 80000
set_option maxHeartbeats 0

theorem certAligned : Form.check denAligned digitsAligned (exprAligned) (repZero) = true := by decide +kernel

end RKResearch.Certified.ERK10FixedQ29Adic.Nonlinear
