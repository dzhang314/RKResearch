module

public import RKCert.ReviewedNative.DIRK10PrimeCRTData

@[expose] public section

namespace RKResearch.Certified.DIRK10PrimeCRT
open RKResearch FiniteRootedTree RingFlagReplay
open scoped Matrix
set_option maxHeartbeats 0
set_option maxRecDepth 36000
set_option Elab.async false

theorem actC0 : blockC 0=true := by decide +kernel
theorem actC1 : blockC 1=true := by decide +kernel
theorem actC2 : blockC 2=true := by decide +kernel
theorem actC3 : blockC 3=true := by decide +kernel
theorem actC4 : blockC 4=true := by decide +kernel
theorem actC5 : blockC 5=true := by decide +kernel
theorem actC6 : blockC 6=true := by decide +kernel
theorem actC7 : blockC 7=true := by decide +kernel
theorem actC8 : blockC 8=true := by decide +kernel

end RKResearch.Certified.DIRK10PrimeCRT
