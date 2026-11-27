module

public import RKCert.ReviewedNative.DIRK10PrimeCRTData

@[expose] public section

namespace RKResearch.Certified.DIRK10PrimeCRT
open RKResearch FiniteRootedTree RingFlagReplay
open scoped Matrix
set_option maxHeartbeats 0
set_option maxRecDepth 36000
set_option Elab.async false

theorem silent0 : blockS 0=true := by decide +kernel
theorem silent1 : blockS 1=true := by decide +kernel
theorem silent2 : blockS 2=true := by decide +kernel
theorem silent3 : blockS 3=true := by decide +kernel
theorem silent4 : blockS 4=true := by decide +kernel
theorem silent5 : blockS 5=true := by decide +kernel
theorem silent6 : blockS 6=true := by decide +kernel
theorem silent7 : blockS 7=true := by decide +kernel
theorem silent8 : blockS 8=true := by decide +kernel
theorem silent9 : blockS 9=true := by decide +kernel

end RKResearch.Certified.DIRK10PrimeCRT
