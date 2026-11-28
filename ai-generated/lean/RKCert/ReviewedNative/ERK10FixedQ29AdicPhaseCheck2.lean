module

public import RKCert.ReviewedNative.ERK10FixedQ29AdicPhaseForms

@[expose] public section

namespace RKResearch.Certified.ERK10FixedQ29Adic.Nonlinear
open Packed

set_option maxRecDepth 80000
set_option maxHeartbeats 0

theorem certMu0 : Form.check denMu0 digitsMu0 (exprMu 0) (repMu 0) = true := by decide +kernel

theorem certMu1 : Form.check denMu1 digitsMu1 (exprMu 1) (repMu 1) = true := by decide +kernel

theorem certMu2 : Form.check denMu2 digitsMu2 (exprMu 2) (repMu 2) = true := by decide +kernel

end RKResearch.Certified.ERK10FixedQ29Adic.Nonlinear
