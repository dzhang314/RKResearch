module

public import RKCert.ReviewedNative.LobattoDIRK109ChecksBase
import Mathlib.Tactic.IntervalCases

@[expose] public section

namespace RKResearch.Certified.LobattoDIRK109

open RKResearch FiniteRootedTree CanonicalStageMemo
open RKCert.ReviewedNative.IntegerHornerCertificate
open RKCert.ReviewedNative.QuadraticHornerReplay
open scoped Matrix FiniteRootedTree

set_option maxHeartbeats 3500000
set_option maxRecDepth 14000

theorem payOK_span480 : checkSpan payOK 480 6 = true := by decide +kernel

end RKResearch.Certified.LobattoDIRK109
