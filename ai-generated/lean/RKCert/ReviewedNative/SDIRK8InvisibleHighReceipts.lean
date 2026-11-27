module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8InvisibleHighReceipts

open scoped BigOperators

/-- A nonzero pair of defect amplitudes with vanishing first and second
signed defect masses must have the same amplitude and cancelling ordinary
weights. This does not use an ordered field. -/
theorem canceledDouble {K : Type*} [Field K] (b₁ b₂ h₁ h₂ : K)
    (hb : b₁ ≠ 0) (hh : h₁ ≠ 0)
    (hm : b₁*h₁+b₂*h₂=0) (hq : b₁*h₁^2+b₂*h₂^2=0) :
    h₁=h₂ ∧ b₁+b₂=0 := by
  have e : (b₁*h₁)*(h₁-h₂)=0 := by linear_combination hq-h₂*hm
  have he := sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_left (mul_ne_zero hb hh))
  have f : (b₁+b₂)*h₁=0 := by rw [← he, ← add_mul] at hm; exact hm
  exact ⟨he,(mul_eq_zero.mp f).resolve_right hh⟩

/-- The weighted transpose sees equal physical cubic defects at a
doubled common clock whose two reverse coordinates cancel. -/
theorem reverseDoubleEqual {K : Type*} [Field K] (r s h k : K)
    (hr : r ≠ 0) (hc : r+s=0) (hh : r*h+s*k=0) : h=k := by
  have he : r*(h-k)=0 := by linear_combination hh-k*hc
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hr)

/-- A polynomial replacement of the defect on all but one actual clock
can change its paid scalar moments only by a single point functional.
No physical row is removed or required to have nonzero aggregate weight. -/
theorem pointDiscrepancy {R ι : Type*} [CommRing R] [Fintype ι]
    (c b h p : ι → R) (z : R) (k : ℕ)
    (he : ∀ i, c i ≠ z → h i=p i) :
    (∑ i,b i*h i*c i^k) - (∑ i,b i*p i*c i^k) =
      (∑ i,b i*(h i-p i))*z^k := by
  rw [← Finset.sum_sub_distrib, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : c i=z
  · rw [hi]; ring
  · simp [he i hi]

#print axioms canceledDouble
#print axioms reverseDoubleEqual
#print axioms pointDiscrepancy

end RKCert.ReviewedNative.SDIRK8InvisibleHighReceipts
