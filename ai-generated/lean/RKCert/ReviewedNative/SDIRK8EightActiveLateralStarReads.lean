module

public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8EightActiveLateralStarReads

def lateralSwap (i : Fin 10) : Fin 10 :=
  if i = 1 then 2 else if i = 2 then 1 else i

theorem lateralSwap_involutive (i : Fin 10) :
    lateralSwap (lateralSwap i) = i := by
  fin_cases i <;> decide

/-- Swapping the adjacent literal front stages preserves triangularity
because the star phase's actual lower coupling is zero. -/
theorem lateralSwapAboveZero {R : Type*} [Zero R]
    (A : Fin 10 → Fin 10 → R)
    (hl : ∀ i j, i < j → A i j = 0) (h₂₃ : A 2 1 = 0) :
    ∀ i j, i < j → A (lateralSwap i) (lateralSwap j) = 0 := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [lateralSwap] at hij ⊢
  all_goals first | exact h₂₃ | exact hl _ _ (by decide)

/-- A vanished quadratic-coefficient resultant has vanished rational
norm, without an order or positivity hypothesis. -/
theorem conjugateNorm {R : Type*} [CommRing R] (u v z : R) (hz : z^2=2) :
    (u+z*v)*(u-z*v)=u^2-2*v^2 := by
  linear_combination -v^2*hz

/-- Coefficient bound and congruence in a sufficiently large product
of CRT primes imply exact equality of the two integer coefficients. -/
theorem boundedCongruent (a b B M : ℤ) (ha : |a|≤B) (hb : |b|≤B)
    (hM : 2*B<M) (hd : M∣a-b) : a=b := by
  apply sub_eq_zero.mp
  apply Int.eq_zero_of_abs_lt_dvd hd
  calc
    |a-b| ≤ |a|+|b| := by simpa [sub_eq_add_neg] using abs_add_le a (-b)
    _ ≤ B+B := add_le_add ha hb
    _ < M := by simpa [two_mul] using hM

#print axioms lateralSwap_involutive
#print axioms lateralSwapAboveZero
#print axioms conjugateNorm
#print axioms boundedCongruent

end RKCert.ReviewedNative.SDIRK8EightActiveLateralStarReads
