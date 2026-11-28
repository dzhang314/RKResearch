module

public import RKCert.ReviewedNative.DIRK12FactorialTwentyFlagData

@[expose] public section

namespace RKResearch.Certified.DIRK12FactorialTwentyFlag
open RKResearch ScaledIntegerFlagReplay FiniteRootedTree
open scoped Matrix
set_option maxRecDepth 50000
set_option maxHeartbeats 0
set_option Elab.async false

theorem actA0 : blockA 0=true := by decide +kernel
theorem actC0 : blockC 0=true := by decide +kernel
theorem actA1 : blockA 1=true := by decide +kernel
theorem actC1 : blockC 1=true := by decide +kernel
theorem actA2 : blockA 2=true := by decide +kernel
theorem actC2 : blockC 2=true := by decide +kernel
theorem actA3 : blockA 3=true := by decide +kernel
theorem actC3 : blockC 3=true := by decide +kernel
theorem actA4 : blockA 4=true := by decide +kernel
theorem actC4 : blockC 4=true := by decide +kernel
theorem actA5 : blockA 5=true := by decide +kernel
theorem actC5 : blockC 5=true := by decide +kernel

end RKResearch.Certified.DIRK12FactorialTwentyFlag
