import RKCert.ReviewedNative.DIRKOrderTwelveFifteenVariableGhostScalar

open Polynomial
open RKResearch.Certified.Graded.OrderTwelveFifteen.VariableGhostScalar

example {K : Type*} [Field K] (a w diag : K) (hw : w ≠ 0) (hwa : w ≠ a)
    (h₁ : (X^2*(X-C a)^2 : K[X]).eval w =
      diag*(X^2*(X-C a)^2 : K[X]).derivative.eval w)
    (h₂ : ((X^2*(X-C a)^2)*(X-C w) : K[X]).eval w =
      diag*((X^2*(X-C a)^2)*(X-C w) : K[X]).derivative.eval w) : False :=
  twoCleanPrimitives a w diag hw hwa h₁ h₂

example {K : Type*} [Field K] (p : K[X]) (a b c : K)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hdeg : p.natDegree ≤ 5)
    (ha : p.IsRoot a ∧ p.derivative.IsRoot a)
    (hb : p.IsRoot b ∧ p.derivative.IsRoot b)
    (hc : p.IsRoot c ∧ p.derivative.IsRoot c) : p = 0 :=
  noThreeDoubleRoots p a b c hab hac hbc hdeg ha hb hc

example {L : Type*} [Field L] [LinearOrder L] [IsStrictOrderedRing L]
    (s t : L) (hs : s ≠ 0) :
    s^5/5 - (s+2*t)*s^4/4 + (2*s*t+t^2)*s^3/3 - s^3*t^2/2 ≠ 0 :=
  spentSign s t hs

#print axioms twoCleanPrimitives
#print axioms noThreeDoubleRoots
#print axioms spentSign
#print axioms cubicMomentLine
#print axioms radauQuarticPrimitive
