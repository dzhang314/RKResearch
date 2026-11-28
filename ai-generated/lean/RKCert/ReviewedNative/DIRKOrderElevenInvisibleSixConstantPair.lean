module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.CharP.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

@[expose] public section
/-! # The guarded constant-ghost terminal-head pair -/
namespace RKResearch.Certified.Graded.OrderElevenInvisibleSixConstantPair

variable {K : Type*} [Field K] [CharZero K]

def J3 (x : K) : K := (2*x-1)*(7*x^2-7*x+1)
def J4 (x : K) : K := 42*x^4-84*x^3+56*x^2-14*x+1
def J5 (x : K) : K := (2*x-1)*(66*x^4-132*x^3+84*x^2-18*x+1)

def pairJacobi (s p : K) : K :=
  2*(2772*p^4-5544*p^3*s+3864*p^3+3696*p^2*s^2-4872*p^2*s+
    1536*p^2-924*p*s^3+1692*p*s^2-972*p*s+172*p+
    66*s^4-144*s^3+108*s^2-32*s+3)

def pairTerminal (s p : K) : K :=
  -28*p^2*s+63*p^2-9*p*s-3*p+s^2

omit [CharZero K] in
/-- The graded head's shift follows from the two literal top
coefficient comparisons. The common head may itself vanish. -/
theorem affine_head_shift (h s l₀ l₁ z : K) (hn : h≠0)
    (h0 : h*l₁+z=0) (h1 : h*l₀-2*h*l₁-z*s=0) :
    l₀=(2-s)*l₁ := by
  have c : h*(l₀-(2-s)*l₁)=0 := by linear_combination h1+s*h0
  exact sub_eq_zero.mp ((mul_eq_zero.mp c).resolve_left hn)

/-- At a root of the ordinary Jacobi pencil the affine head
times the quartic equals the next lower Jacobi polynomial. -/
theorem recurrence_at_pencil (s l : K) (h : J5 s+l*J4 s=0) :
    (s-(1/2-7*l/22))*J4 s=(2/11)*J3 s := by
  unfold J3 J4 J5 at *
  linear_combination (7/22:K)*h

omit [CharZero K] in
/-- Clearing the diagonal factor a-b retains every distinct pair. -/
theorem pair_jacobi_identity (a b : K) :
    J5 a * J4 b - J5 b * J4 a = (a-b)*pairJacobi (a+b) (a*b) := by
  unfold J5 J4 pairJacobi
  ring

omit [CharZero K] in
/-- No division by either primitive numerator appears in the
nonzero-clock terminal comparison. -/
theorem pair_terminal_identity (a b : K) :
    a^2*(2*b-a)*J3 b - b^2*(2*a-b)*J3 a =
      (a-b)*pairTerminal (a+b) (a*b) := by
  unfold J3 pairTerminal
  ring

omit [CharZero K] in
theorem pair_from_paid_heads (a b h q l : K)
    (a0 : a≠0) (b0 : b≠0) (ab : a≠b) (h0 : h≠0)
    (r0 : h*a^3*(2*b-a)=q*a*J3 a)
    (r1 : h*b^3*(2*a-b)=q*b*J3 b)
    (p0 : J5 a+l*J4 a=0) (p1 : J5 b+l*J4 b=0) :
    pairJacobi (a+b) (a*b)=0 ∧ pairTerminal (a+b) (a*b)=0 := by
  have f : J5 a*J4 b-J5 b*J4 a=0 := by
    linear_combination J4 b*p0-J4 a*p1
  rw [pair_jacobi_identity] at f
  refine ⟨(mul_eq_zero.mp f).resolve_left (sub_ne_zero.mpr ab),?_⟩
  have g : h*a*b*(a^2*(2*b-a)*J3 b-b^2*(2*a-b)*J3 a)=0 := by
    linear_combination (b*J3 b)*r0-(a*J3 a)*r1
  rw [pair_terminal_identity] at g
  exact (mul_eq_zero.mp ((mul_eq_zero.mp g).resolve_left
    (mul_ne_zero (mul_ne_zero h0 a0) b0))).resolve_left (sub_ne_zero.mpr ab)

end RKResearch.Certified.Graded.OrderElevenInvisibleSixConstantPair
