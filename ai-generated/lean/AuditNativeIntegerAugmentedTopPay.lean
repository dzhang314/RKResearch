module

import RKResearch.OrderConditions
import RKCert.ReviewedNative.NativeIntegerAugmentedTopPay

namespace RKCert.Audit.NativeIntegerAugmentedTopPay

open RKResearch
open RKResearch.Certified.NativeIntegerSpanClearing
open RKResearch.Certified.NativeIntegerAugmentedChecker
open RKResearch.Certified.NativeIntegerAugmentedTopPay
open scoped Matrix

example {s p : ℕ} (A : Matrix (Fin s) (Fin s) ℤ) (b : ZVec s)
    (d e : ℤ) (C : Candidate s)
    (U : Matrix (Fin s) (Fin s) ℚ) (w : Fin s → ℚ)
    (hA : ratMatrix A = (d : ℚ) • U) (hb : ratVec b = (e : ℚ) • w)
    (h : checkDirectTop (fun v => A *ᵥ v) (fun v => b ⬝ᵥ v) d e p C = true) :
    RKResearch.HasOrder p U w :=
  hasOrder_of_direct_top_check A b _ _ (fun _ => rfl) (fun _ => rfl) d e p C hA hb h

#check @checkDirectTop_iff
#check @basisCloses_with_direct_top
#print axioms checkTopPayments_sound
#print axioms hasOrder_of_direct_top_check

end RKCert.Audit.NativeIntegerAugmentedTopPay
