module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.CharZero.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKResearch.Certified.ERK149TwoPairChronology

variable {K : Type*} [Field K] [CharZero K]

def G (a b s : K) : K :=
  (a+b)*s^3/3-a*b*s^2/2-s^4/4

def T (a b s : K) : K :=
  s^2*(2*s-3*a)/(6*b*(b-a))

/-- The exact pooled determinant when a pair completes before the first
new singleton. The next group may be the other completed pair. -/
theorem complete_first_minor (a b c : K) (hb : b ≠ 0) (hab : a ≠ b) :
    G a b a * T a b c - G a b c * T a b a =
      a^3*c^2*(a-c)^2/(24*b*(a-b)) := by
  unfold G T
  have h1 : a-b ≠ 0 := sub_ne_zero.mpr hab
  have h2 : b-a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  field_simp
  ring

/-- The exact weighted-pool determinant when the first singleton
precedes the first completed pair. Only the two already paid lower
moments of the next pooled row are needed. -/
theorem singleton_first_minor (c s r q : K)
    (h₁ : r*c^2/2+q*c=s^2/2)
    (h₂ : r*c^3/3+q*c^2=s^3/3) :
    q*c^3-s^4/4+r*c^4/4 = -s^2*(s-c)^2/4 := by
  linear_combination (3*c/2)*h₂ - (c^2/2)*h₁

/-- The first second-pair response in the three-unary reverse word:
the arbitrary incoming tap cancels exactly. -/
theorem second_pair_word (a b k : K) :
    (k*a^2-b^3/3)/2 + k*(-a^2/2) = -b^3/6 := by
  ring

end RKResearch.Certified.ERK149TwoPairChronology
