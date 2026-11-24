module

public import RKCert.ReviewedNative.LobattoDIRK88PayCheck140
import Mathlib.Tactic.IntervalCases

@[expose] public section

namespace RKResearch.Certified.LobattoDIRK88

open RKResearch FiniteRootedTree CanonicalStageMemo
open RKCert.ReviewedNative.IntegerHornerCertificate
open RKCert.ReviewedNative.QuadraticHornerReplay
open scoped Matrix FiniteRootedTree

set_option maxHeartbeats 2800000
set_option maxRecDepth 12000

theorem payOK_span160 : checkSpan payOK 160 20 = true := by decide +kernel

end RKResearch.Certified.LobattoDIRK88
