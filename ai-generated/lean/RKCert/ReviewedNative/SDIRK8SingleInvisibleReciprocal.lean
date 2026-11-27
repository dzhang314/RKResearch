module

public import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8SingleInvisibleReciprocal

/-- The actual normalized pure reverse ratio becomes reciprocal to the
ordinary signed weight numerator when the reverse numerator is constant. -/
theorem reciprocalReverse {K : Type*} [Field K]
    (bi bx di dx wi wx t k : K) (ht : t≠0)
    (hi : di*wi=t) (hx : dx*wx=t)
    (hr : wi*bx=k*wx*bi) : k*(bi*di)=bx*dx := by
  have e : t*(k*(bi*di)-bx*dx)=0 := by
    linear_combination -k*(bi*di)*hx+(bx*dx)*hi-(di*dx)*hr
  exact sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_left ht)

/-- One missing, nonzero signed atomic mass makes the first two masked
moments determine its actual clock without a sign assumption. -/
theorem oneMissingClock {K : Type*} [Field K]
    (b x p m₀ m₁ : K) (hb : b≠0) (hp : p≠0)
    (h₀ : m₀=b*p) (h₁ : m₁=b*p*x) :
    m₀≠0 ∧ m₀*x=m₁ := by
  rw [h₀,h₁]
  exact ⟨mul_ne_zero hb hp,rfl⟩

/-- Removing one marked clock from the numerator cancels its clock
parameter from the quadratic masked weight expression. -/
theorem reciprocalTailCancellation {R : Type*} [CommRing R]
    (c d a₀ a₁ a₂ a₃ : R) :
    ((a₂-d*a₁)-c*(a₁-d*a₀))*(a₂-d*a₁)-
    ((a₃-d*a₂)-c*(a₂-d*a₁))*(a₁-d*a₀)=
    (a₂-d*a₁)^2-(a₃-d*a₂)*(a₁-d*a₀) := by ring

#print axioms reciprocalReverse
#print axioms oneMissingClock
#print axioms reciprocalTailCancellation

end RKCert.ReviewedNative.SDIRK8SingleInvisibleReciprocal
