module

public import RKCert.ReviewedNative.ERK10FixedQ29AdicHeadForms

@[expose] public section

namespace RKResearch.Certified.ERK10FixedQ29Adic.Nonlinear
open Packed

set_option maxRecDepth 80000
set_option maxHeartbeats 0

theorem certK : Form.check denK digitsK exprK repK = true := by decide +kernel

theorem certQC : Form.check denQC digitsQC exprQC repQC = true := by decide +kernel

theorem certE0 : Form.check denE0 digitsE0 exprE0 repE0 = true := by decide +kernel

theorem certE1 : Form.check denE1 digitsE1 exprE1 repE1 = true := by decide +kernel

theorem certBeta : Form.check denBeta digitsBeta exprBeta repZero = true := by decide +kernel

end RKResearch.Certified.ERK10FixedQ29Adic.Nonlinear
