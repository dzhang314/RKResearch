import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

namespace RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixAlphaOneBetaZeroFifthPivot

theorem zero_diagonal_of_first_support {K : Type*} [CommRing K] [IsDomain K]
    {d w : K} (hw : w ≠ 0) (h : -(d * d) * w = 0) : d = 0 := by
  have hj : -(d * d) = 0 := (mul_eq_zero.mp h).resolve_right hw
  have hm : d * d = 0 := neg_eq_zero.mp hj
  exact (mul_eq_zero.mp hm).elim id id

theorem jacobi_contact_absurd {K : Type*} [Field K] [CharZero K]
    (z : K)
    (hP : 3564*z^4 - 5544*z^3 + 2832*z^2 - 566*z + 33 = 0)
    (hQ : 182952*z^5 - 548856*z^4 + 519288*z^3 - 199584*z^2 + 31817*z - 1590 = 0) :
    False := by
  have h : (26396875886920749 : K) = 0 := by
    linear_combination (844805049730488*z^4 - 192776280116117544*z^3 +
       488058578234024952*z^2 - 315368371833036984*z + 46455276093351553) * hP +
       (-16457241228516*z^3 + 3731610509520696*z^2 -
        4120873737341448*z + 947564298863950) * hQ
  exact (by norm_num : (26396875886920749 : K) ≠ 0) h

end RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixAlphaOneBetaZeroFifthPivot

open RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixAlphaOneBetaZeroFifthPivot
#print axioms zero_diagonal_of_first_support
#print axioms jacobi_contact_absurd
