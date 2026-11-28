module

public import RKCert.ReviewedNative.ERK10FixedQ29AdicPhaseForms

@[expose] public section

namespace RKResearch.Certified.ERK10FixedQ29Adic.Nonlinear
open Packed

set_option maxRecDepth 80000
set_option maxHeartbeats 0

theorem certMu3 : Form.check denMu3 digitsMu3 (exprMu 3) (repMu 3) = true := by decide +kernel

theorem certMu4 : Form.check denMu4 digitsMu4 (exprMu 4) (repMu 4) = true := by decide +kernel

theorem certMu5 : Form.check denMu5 digitsMu5 (exprMu 5) (repMu 5) = true := by decide +kernel

end RKResearch.Certified.ERK10FixedQ29Adic.Nonlinear
