module

public import RKCert.ReviewedNative.ERK10FixedQ29AdicPhaseForms

@[expose] public section

namespace RKResearch.Certified.ERK10FixedQ29Adic.Nonlinear
open Packed

set_option maxRecDepth 80000
set_option maxHeartbeats 0

theorem certMu6 : Form.check denMu6 digitsMu6 (exprMu 6) (repMu 6) = true := by decide +kernel

end RKResearch.Certified.ERK10FixedQ29Adic.Nonlinear
