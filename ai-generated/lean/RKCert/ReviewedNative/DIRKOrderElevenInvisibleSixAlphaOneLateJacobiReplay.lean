/-! Exact integer coefficient checks for the late homogeneous Jacobi line.
Mathlib-independent; all statements are reduced by the ordinary kernel. -/

namespace RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixAlphaOneLateJacobiReplay

private def det3 (a b c d e f g h i : Int) : Int :=
  a*(e*i-f*h)-b*(d*i-f*g)+c*(d*h-e*g)

private def gram : Int :=
  210*det3 42 24 15 24 15 10 15 10 7
    -84*det3 84 24 15 42 15 10 24 10 7
    +42*det3 84 42 15 42 24 10 24 15 7
    -24*det3 84 42 24 42 24 15 24 15 10

/-- The four by four weighted moment Gram determinant after scaling by 2520. -/
theorem gram_det : gram = 18 := by decide

private def weighted (a b c d e : Int) : Int :=
  a-16*b+72*c-120*d+66*e

/-- The four normalized ordinary moments, now on the common scale 27720. -/
theorem endpoint_orthogonal :
    weighted 2310 924 462 264 165 = 0 ∧
    weighted 924 462 264 165 110 = 0 ∧
    weighted 462 264 165 110 77 = 0 ∧
    weighted 264 165 110 77 56 = 0 := by decide

private def em : List Int := [1,-16,72,-120,66]
private def j4 : List Int := [1,-14,56,-84,42,0]
private def j5 : List Int := [-1,20,-120,300,-330,132]

/-- Equality of all six coefficients of 2(Y−1) E_- = J5−J4. -/
theorem endpoint_factor_coefficients :
    List.zipWith (fun a b : Int => 2*(a-b)) (0::em) (em++[0]) =
    List.zipWith (fun a b : Int => a-b) j5 j4 := by decide

#print axioms gram_det
#print axioms endpoint_orthogonal
#print axioms endpoint_factor_coefficients

end RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixAlphaOneLateJacobiReplay
