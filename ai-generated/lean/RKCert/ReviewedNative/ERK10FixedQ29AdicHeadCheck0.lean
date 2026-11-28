module

public import RKCert.ReviewedNative.ERK10FixedQ29AdicHeadForms

@[expose] public section

namespace RKResearch.Certified.ERK10FixedQ29Adic.Nonlinear
open Packed

set_option maxRecDepth 80000
set_option maxHeartbeats 0

theorem certH : Form.check denH digitsH exprH repZero = true := by decide +kernel

theorem certF : Form.check denF digitsF exprF repZero = true := by decide +kernel

theorem certE : Form.check denE digitsE exprE repZero = true := by decide +kernel

end RKResearch.Certified.ERK10FixedQ29Adic.Nonlinear
