module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

@[expose] public section

/-! # Exact grade-seven forward and unordered reverse mark adapters -/
namespace RKResearch.Certified.Graded.OrderElevenInvisibleSixQuadraticClosure

open Polynomial
open scoped BigOperators

variable {K : Type*} [Field K] [CharZero K]

def J4 (x : K) : K := 42*x^4-84*x^3+56*x^2-14*x+1
def J5 (x : K) : K := (2*x-1)*(66*x^4-132*x^3+84*x^2-18*x+1)
noncomputable def IH (x : K) : K :=
  7*x^6-(84/5)*x^5+14*x^4-(14/3)*x^3+x^2/2

/-- The Jacobi identity used before reduction by the monic
quadratic carrier. It has no divisor depending on a clock. -/
theorem primitive_jacobi_hull (x l : K) :
    IH x-x*J4 x*(-x/5+7*(1-l)/60)=
      (77/5)*(x*(J5 x+l*J4 x)/132) := by
  unfold IH J4 J5
  ring

omit [CharZero K] in
/-- Project a paid proportionality through a second coefficient read.
There is no division by the leading shift on the left. -/
theorem forward_remainder_factor (f₀ f₁ s₀ s₁ x₀ x₁ c r d : K)
    (prop : f₀*s₁-f₁*s₀=0)
    (h₀ : c*f₀=r*s₀+d*x₀) (h₁ : c*f₁=r*s₁+d*x₁) :
    d*(x₀*s₁-x₁*s₀)=0 := by
  linear_combination c*prop-s₁*h₀+s₀*h₁

omit [CharZero K] in
/-- This is the guarded diagonal/remainder split. Zero contacts
of the primitive at a clock have nowhere been inverted. -/
theorem diagonal_or_remainder (d a u h det : K)
    (an : a≠0) (un : u≠0) (hn : h≠0)
    (hdet : (d^2*a*u/h)*det=0) : d=0 ∨ det=0 := by
  by_cases dz : d=0
  · exact Or.inl dz
  · exact Or.inr ((mul_eq_zero.mp hdet).resolve_left
      (div_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 dz) an) un) hn))

noncomputable def cubic (a b c y : K) : K := a*y+b*y^2+c*y^3
noncomputable def primitiveCubic (a b c y : K) : K :=
  a*y^2/2+b*y^3/3+c*y^4/4

/-- Weighted transpose taps paid through degree three: against any
cubic with zero constant the actual correction is affine times
the cubic row when the degree-four primitive is affine times it. -/
theorem sum_cubic_mark {ι : Type*} [Fintype ι] (T y : ι→K)
    (a b c s L k : K)
    (h₁ : ∑ i, T i*y i=s^2/2)
    (h₂ : ∑ i, T i*(y i)^2=s^3/3+k)
    (h₃ : ∑ i, T i*(y i)^3=s^4/4+L*k) :
    (∑ i, T i*cubic a b c (y i))=primitiveCubic a b c s+(b+c*L)*k := by
  calc
    (∑ i, T i*cubic a b c (y i)) =
        a*(∑ i,T i*y i)+b*(∑ i,T i*(y i)^2)+c*(∑ i,T i*(y i)^3) := by
      simp only [Finset.mul_sum,←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      unfold cubic
      ring
    _ = _ := by
      rw [h₁,h₂,h₃,primitiveCubic]
      ring

omit [CharZero K] in
/-- Equality of an affine read and its quadratic interpolation on
three distinct old clocks kills the quadratic coefficient. -/
theorem affine_remainder_coeff (P : K[X]) (pd : P.natDegree≤2)
    (s : Fin 3→K) (inj : Function.Injective s) (a b : K)
    (ht : ∀ i, P.eval (s i)=a+b*s i) : P.coeff 2=0 := by
  let Q : K[X] := C a+C b*X
  have qd : Q.natDegree≤1 := by
    have d : (C b*X).natDegree≤1 :=
      (natDegree_mul_le (p:=C b) (q:=X)).trans (by rw [natDegree_C,natDegree_X,zero_add])
    simpa [Q] using (natDegree_add_le_of_le (p:=C a) (q:=C b*X)
      (show (C a).natDegree≤1 by simp) d)
  have z : P=Q := eq_of_natDegree_lt_card_of_eval_eq P Q inj
    (fun i => by simpa [Q] using ht i) (by rw [Fintype.card_fin]; omega)
  rw [z,coeff_eq_zero_of_natDegree_lt (by omega)]

omit [CharZero K] in
/-- Only its own inclusive diagonal changes the interpolated mark
at the next regular clock, which gives the unordered fourth read. -/
theorem fourth_symmetric_mark (p raw off k R L d new old : K)
    (core : raw=p+off*k)
    (read : raw+d*(new-old)=L*k)
    (fit : R=L-off) :
    p-R*k+d*(new-old)=0 := by
  linear_combination read-core-k*fit

end RKResearch.Certified.Graded.OrderElevenInvisibleSixQuadraticClosure
