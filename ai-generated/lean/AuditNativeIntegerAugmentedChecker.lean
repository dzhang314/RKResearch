module

import RKResearch.OrderConditions
import RKCert.ReviewedNative.NativeIntegerAugmentedChecker

namespace RKCert.Audit.NativeIntegerAugmentedChecker

open RKResearch
open RKResearch.Certified.NativeIntegerSpanClearing
open RKResearch.Certified.NativeIntegerAugmentedChecker
open scoped Matrix

example {s p : ℕ} (A : Matrix (Fin s) (Fin s) ℤ) (b : ZVec s)
    (d e : ℤ) (C : Candidate s)
    (h : check (fun v => A *ᵥ v) (fun v => b ⬝ᵥ v) d e p C = true) :
    RKResearch.HasOrder p (normalizedA A d) (normalizedb b e) :=
  hasOrder_of_dense_check A b d e p C h

#check @check_iff
#check @checkProducts_sound
#check @hasOrder_of_check
#print axioms joinedZ_sound
#print axioms hasOrder_of_check
#print axioms hasOrder_of_dense_check

end RKCert.Audit.NativeIntegerAugmentedChecker
