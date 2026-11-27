module

public import RKResearch.OrderConditions
public import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Denominator-free scalar gates for the order-eight ten-stage problem
These lemmas do not assume ordered coefficients or positivity. They are
independent of the tagged tableau census and Newton localization. -/
namespace RKResearch.Certified.ERK8UnorderedScalarGates

open scoped Matrix BigOperators

variable {ι R : Type*} [Fintype ι] [CommRing R] [Nontrivial R]

/-- A four-site degree-seven quadrature with a prescribed endpoint at
one is impossible even over a nontrivial commutative ring. The other
three listed sites may repeat or have zero aggregate mass. -/
theorem no_four_sites_at_one {b c : ι → R} (ho : HasQuadratureOrder 8 b c)
    (a d e : R) (loc : ∀ i, b i=0 ∨ c i=1 ∨ c i=a ∨ c i=d ∨ c i=e) :
    False := by
  let m (k : Nat) := ∑ i, b i * (c i)^k
  let D₀ := -a*d*e
  let D₁ := a*d+a*e+d*e
  let D₂ := -(a+d+e)
  have M (k : Nat) (hk : k<8) : ((k:R)+1)*m k=1 := by
    simpa only [m,dotProduct,Pi.pow_apply,Nat.cast_succ] using ho k hk
  have beta (j : Nat) (hj : j≤6) :
      ((j:R)+1)*((j:R)+2)*(m j-m (j+1))=1 := by
    have u := M j (by omega)
    have v := M (j+1) (by omega)
    simp only [Nat.cast_add,Nat.cast_one] at v
    linear_combination ((j:R)+2)*u-((j:R)+1)*v
  have z (k : Nat) : D₀*(m k-m (k+1)) + D₁*(m (k+1)-m (k+2)) +
      D₂*(m (k+2)-m (k+3))+(m (k+3)-m (k+4))=0 := by
    simp only [m,Finset.mul_sum,←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro i _
    have x :
        (D₀*(b i*c i^k-b i*c i^(k+1))+
          D₁*(b i*c i^(k+1)-b i*c i^(k+2))+
          D₂*(b i*c i^(k+2)-b i*c i^(k+3))+
          (b i*c i^(k+3)-b i*c i^(k+4))) =
        b i*c i^k*(1-c i)*(c i-a)*(c i-d)*(c i-e) := by
      simp only [D₀,D₁,D₂,pow_add]
      ring
    rw [x]
    rcases loc i with h|h|h|h|h <;> simp [h]
  have B₀ := beta 0 (by decide)
  have B₁ := beta 1 (by decide)
  have B₂ := beta 2 (by decide)
  have B₃ := beta 3 (by decide)
  have B₄ := beta 4 (by decide)
  have B₅ := beta 5 (by decide)
  have B₆ := beta 6 (by decide)
  norm_num at B₀ B₁ B₂ B₃ B₄ B₅ B₆
  have c₀ : 30*D₀+10*D₁+5*D₂+3=0 := by
    linear_combination 60*z 0 - 30*D₀*B₀ -10*D₁*B₁-5*D₂*B₂-3*B₃
  have c₁ : 10*D₀+5*D₁+3*D₂+2=0 := by
    linear_combination 60*z 1 - 10*D₀*B₁ -5*D₁*B₂-3*D₂*B₃-2*B₄
  have c₂ : 35*D₀+21*D₁+14*D₂+10=0 := by
    linear_combination 420*z 2 - 35*D₀*B₂ -21*D₁*B₃-14*D₂*B₄-10*B₅
  have c₃ : 42*D₀+28*D₁+20*D₂+15=0 := by
    linear_combination 840*z 3 - 42*D₀*B₃ -28*D₁*B₄-20*D₂*B₅-15*B₆
  have no : (3:R)=0 := by linear_combination -14*c₀+210*c₁-90*c₂+35*c₃
  exact (HasQuadratureOrder.isUnit (n:=3) ho (by decide) (by decide)).ne_zero
    (by simpa using no)

variable {K : Type*} [Field K]

/-- The degree-three Lobatto factor has no root whose double is another
root in any field in which 5 and 7 are nonzero. -/
theorem no_lobatto_double (five : (5:K)≠0) (seven : (7:K)≠0) {t : K}
    (h : (2*t-1)*(7*t^2-7*t+1)=0)
    (h2 : (2*(2*t)-1)*(7*(2*t)^2-7*(2*t)+1)=0) : False := by
  rcases mul_eq_zero.mp h with hl | hq
  · rw [sub_eq_zero.mp hl] at h2
    have e : (1:K)=0 := by linear_combination h2
    exact one_ne_zero e
  · rcases mul_eq_zero.mp h2 with hl | hq2
    · have e : (5:K)=0 := by
        linear_combination (7*(4*t+1)-28)*hl -16*hq
      exact five e
    · have ht : 14*t-3=0 := by linear_combination hq2-4*hq
      have hz : (7:K)*5=0 := by
        linear_combination (7*(14*t+3)-98)*ht -196*hq
      exact mul_ne_zero seven five hz

end RKResearch.Certified.ERK8UnorderedScalarGates

#print axioms RKResearch.Certified.ERK8UnorderedScalarGates.no_four_sites_at_one
#print axioms RKResearch.Certified.ERK8UnorderedScalarGates.no_lobatto_double
