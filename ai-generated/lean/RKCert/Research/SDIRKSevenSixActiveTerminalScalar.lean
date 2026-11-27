module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.CharZero.Defs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Denominator-cleared terminal split in the cubic-dirty nine-stage chart -/
namespace RKResearch.Certified.SDIRKSevenSixActiveTerminalScalar

variable {K : Type*} [Field K] [CharZero K]

def L₂ (u : K) : K := u^2/2-2*u+1

def M (u : K) : K := u^2-4*u+2

def mf (u v : K) : K := -4*M u+(2-2*M u)*(v-1)

/-- These are the three reverse equations after cancelling the known
nonzero weight and clearing 2, 3 and the nonzero penultimate error
scale. The proof never divides by the other linear determinant. -/
theorem two_branches {u v p d : K}
    (n₁ : u≠1) (n₂ : u≠v) (n₃ : v≠1) (nM : M u≠0)
    (h₁ : (u-1)*p=L₂ v-d)
    (h₂ : 3*M u*(v^2+v-1-v^3/3+p*(u^2-1))=mf u v*d)
    (h₃ : M u*((M u+1)*p-(v-1))=2*(1-v)*d) :
    v=4-u ∨ v=2*u-1 := by
  let a₀ := 3*M u*(v^2+v-1-v^3/3+(u+1)*L₂ v)
  let a₁ := -(3*M u*(u+1)+mf u v)
  let b₀ := M u*(M u+1)*L₂ v-M u*(v-1)*(u-1)
  let b₁ := -M u*(M u+1)-2*(u-1)*(1-v)
  have a : a₀+a₁*d=0 := by
    dsimp only [a₀,a₁]
    linear_combination h₂-3*M u*(u+1)*h₁
  have b : b₀+b₁*d=0 := by
    dsimp only [b₀,b₁]
    linear_combination (u-1)*h₃-M u*(M u+1)*h₁
  have z : b₁*a₀-a₁*b₀=0 := by linear_combination b₁*a-a₁*b
  have fact : b₁*a₀-a₁*b₀=-2*(u-1)*(u-v)*(v-1)*(u+v-4)*(2*u-v-1)*M u := by
    dsimp [a₀,a₁,b₀,b₁,mf,M,L₂]
    ring
  rw [fact] at z
  have first : u+v-4=0 ∨ 2*u-v-1=0 := by
    by_contra q
    push Not at q
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (mul_ne_zero (by norm_num : (-2:K)≠0) (sub_ne_zero.mpr n₁))
      (sub_ne_zero.mpr n₂)) (sub_ne_zero.mpr n₃)) q.1) q.2) nM) z
  rcases first with h | h
  · left; linear_combination h
  · right; linear_combination -h

/-- At the reflection branch u=0, the fourth reverse row is one
cleared Laguerre scalar equation, with no extra determinant. -/
theorem fourth_at_zero (c d : K) :
    (c^3/3-c^2+(-1-c/3)*d)/2-2*(c^2/2-c-d)+(c-1)-(1-c)*d/2 =
      (2*(c+3)*d+c^3-9*c^2+18*c-6)/6 := by ring

end RKResearch.Certified.SDIRKSevenSixActiveTerminalScalar
