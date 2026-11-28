module

public import RKCert.ReviewedNative.DIRK12FactorialTwentyFlagData

@[expose] public section

namespace RKResearch.Certified.DIRK12FactorialTwentyFlag
open RKResearch ScaledIntegerFlagReplay FiniteRootedTree
open scoped Matrix
set_option maxRecDepth 50000
set_option maxHeartbeats 0
set_option Elab.async false

theorem actA6 : blockA 6=true := by decide +kernel
theorem actC6 : blockC 6=true := by decide +kernel
theorem actA7 : blockA 7=true := by decide +kernel
theorem actC7 : blockC 7=true := by decide +kernel
theorem actA8 : blockA 8=true := by decide +kernel
theorem actC8 : blockC 8=true := by decide +kernel
theorem actA9 : blockA 9=true := by decide +kernel
theorem actC9 : blockC 9=true := by decide +kernel
theorem actA10 : blockA 10=true := by decide +kernel
theorem actC10 : blockC 10=true := by decide +kernel

end RKResearch.Certified.DIRK12FactorialTwentyFlag
