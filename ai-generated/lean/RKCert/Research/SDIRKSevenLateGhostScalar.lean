module

public import Mathlib.Algebra.Field.Rat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Literal late-ghost reverse and affine-helper gates -/

namespace RKResearch.Certified.SDIRKSevenLateGhostScalar

def M (u : ℚ) : ℚ := u^2-4*u+2
def T (u : ℚ) : ℚ := u^3-7*u^2+10*u-2
def f (u h : ℚ) : ℚ := -4/3+(2/M u-2)*(h-1)/3

/-- A ghost with exactly two nonzero-output successors in the
normalized dirty reverse chart forces the singular cubic. -/
theorem two_taps_factor {u h p δ : ℚ} (hd : δ≠0) (hm : M u≠0)
    (r₂ : (u-1)*p = -δ)
    (r₃ : (u^2-1)*p=f u h*δ)
    (r₄ : (M u+1)/2*p=(1-h)/M u*δ) :
    (u-1)*T u=0 := by
  have he : (f u h+(u+1))*δ=0 := by
    linear_combination (u+1)*r₂-r₃
  have h₃ : f u h+(u+1)=0 := (mul_eq_zero.mp he).resolve_right hd
  unfold f at h₃
  have e₃ : 2*(1-M u)*(h-1)+M u*(3*u-1)=0 := by
    field_simp [hm] at h₃
    linear_combination h₃
  have e₄prod : (2*(u-1)*(h-1)-M u*(M u+1))*δ=0 := by
    field_simp [hm] at r₄
    linear_combination (u-1)*r₄-M u*(M u+1)*r₂
  have e₄ := (mul_eq_zero.mp e₄prod).resolve_right hd
  have out : M u*((u-1)*T u)=0 := by
    simp only [M,T] at e₃ e₄ ⊢
    linear_combination -(u-1)*e₃+(1-(u^2-4*u+2))*e₄
  exact (mul_eq_zero.mp out).resolve_left hm

def ratioQ (a b c y : ℚ) : ℚ := a+b*y+c*y^2

/-- The three active reverse successors determine their fourth
read by the quadratic interpolant of their ratios. -/
theorem three_taps_gate {y z w p q r a b c δ ϕ θ h : ℚ} (hd : δ≠0)
    (r₁ : p+q+r=0)
    (r₂ : y*p+z*q+w*r= -δ)
    (r₃ : y^2*p+z^2*q+w^2*r=ϕ*δ)
    (r₄ : ratioQ a b c y*p+ratioQ a b c z*q+ratioQ a b c w*r=
      θ*(1-h)*δ) :
    -b+c*ϕ-θ*(1-h)=0 := by
  simp only [ratioQ] at r₄
  have hz : (-b+c*ϕ-θ*(1-h))*δ=0 := by
    linear_combination r₄-a*r₁-b*r₂-c*r₃
  exact (mul_eq_zero.mp hz).resolve_right hd

theorem reflection_ghost_pin {u h : ℚ} (hm : M u≠0)
    (read : 2+f u h/2-(1-h)/M u=0) :
    4-M u≠0 ∧ h=(4-5*M u)/(4-M u) := by
  unfold f at read
  have e : (4-M u)*h=4-5*M u := by
    field_simp [hm] at read
    linear_combination read/2
  have hD : 4-M u≠0 := by
    intro d
    have h4 : M u=4 := by linear_combination -d
    rw [d,zero_mul,h4] at e
    norm_num at e
  exact ⟨hD,(eq_div_iff hD).mpr (by rw [mul_comm]; exact e)⟩

def U (x : ℚ) : ℚ := x^3/3-2*x^2+3*x-1
def V (x : ℚ) : ℚ := x^2/2-2*x+1
def gap (t x : ℚ) : ℚ :=
  x^3/3-(2+t)*x^2/2+(1+t)*x-(x-1)*(x-1-t)

theorem helper_gap (t x : ℚ) : gap t x=U x-t*V x := by
  simp only [gap,U,V]
  ring

/-- At a first active clock equal to one, the second stage's two
forward reads recover the helper tap affinely, not quadratically. -/
theorem affine_helper {t x lam : ℚ} (pivot : V x+lam/2≠0)
    (read : gap t x=lam*gap t 1) :
    t=(U x-lam/3)/(V x+lam/2) := by
  simp only [helper_gap] at read
  have a : U 1=1/3 := by norm_num [U]
  have b : V 1= -1/2 := by norm_num [V]
  rw [a,b] at read
  apply (eq_div_iff pivot).mpr
  linear_combination -read

end RKResearch.Certified.SDIRKSevenLateGhostScalar
