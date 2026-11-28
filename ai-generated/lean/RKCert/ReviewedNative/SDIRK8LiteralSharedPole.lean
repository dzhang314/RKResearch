module

public import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8LiteralSharedPole

/-- An individual silent stage at the rational pole has its own
defect. Match strict-five's actual affine difference at that clock,
then transfer only the difference slope to the actual fourth row. -/
theorem literalPoleFourthCut {K : Type*} [Field K]
    (a b s hb hj hs vb vj vs τ μ X D : K)
    (hsa : s - a ≠ 0) (hjb : hj - hb ≠ 0)
    (hactiveFourth : vs = (τ + (s-a)*μ) * hs)
    (hfourthDivided : vs - τ * hs = (s-a)*X)
    (hactualDiff : vj-vb = D*(hj-hb))
    (hpaidDiff : vj-vb = (τ+(b-a)*μ)*(hj-hb)) :
    hs*(D-τ) = X*(b-a) := by
  have H₀ : (μ*hs-X)*(s-a) = 0 := by
    linear_combination hfourthDivided - hactiveFourth
  have H₁ : (D - (τ+(b-a)*μ)) * (hj-hb) = 0 := by
    linear_combination hpaidDiff - hactualDiff
  have ha' := (mul_eq_zero.mp H₀).resolve_right hsa
  have hd' := (mul_eq_zero.mp H₁).resolve_right hjb
  linear_combination hs * hd' + (b-a) * ha'

/-- The cleared fifth read has no division by the fourth defect,
the current rational defect denominator, or a silent stage weight. -/
theorem clearedFifthRead {R : Type*} [CommRing R]
    (a s h H Q P v₀ D τ μ X : R)
    (hs : μ*H = X)
    (hq : Q*h = P)
    (hread : v₀ + D*h = (τ + (s-a)*μ)*h) :
    H*v₀*Q + (H*(D-τ)-X*(s-a))*P = 0 := by
  linear_combination (H*Q)*hread + ((s-a)*Q*h)*hs +
    (X*(s-a)-H*(D-τ))*hq

#print axioms literalPoleFourthCut
#print axioms clearedFifthRead

end RKCert.ReviewedNative.SDIRK8LiteralSharedPole
