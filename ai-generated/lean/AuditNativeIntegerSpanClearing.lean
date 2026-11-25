module

import RKCert.ReviewedNative.NativeIntegerSpanClearing

namespace RKCert.Audit.NativeIntegerSpanClearing

open RKResearch.Certified.NativeIntegerSpanClearing

example {s r : ℕ} (rows : Fin r → ZFeature s) (x : ZFeature s)
    (record : Clearing r) (h : checkClearing rows x record = true) :
    ratFeature x ∈ Submodule.span ℚ (Set.range (fun i => ratFeature (rows i))) :=
  checkClearing_sound h

#check @checkClearing
#check @checkClearing_sound
#print axioms sparseSum_mem_span
#print axioms checkClearing_sound

end RKCert.Audit.NativeIntegerSpanClearing
