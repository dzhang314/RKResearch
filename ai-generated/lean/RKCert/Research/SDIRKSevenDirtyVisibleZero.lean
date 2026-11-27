module

public import RKCert.Research.SDIRKSevenDirtyArithmeticAtlas
public import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Scalar gates for a vanishing visible cubic at the sixth active clock

These lemmas protect the reciprocal suffix cut, including singular
Christoffel moment pivots.  The stage-to-Gram reduction, genus and
degree computation for the curve are separate. -/

namespace RKResearch.Certified.SDIRKSevenDirtyVisibleZero
open SDIRKSevenDirtyArithmeticAtlas

section field
variable {K : Type*} [Field K]

def cut (u c : K) : K :=
  6*(u-2)*(u-1)^2*(c-1)-
    3*(u-3)*(u-1)*(2*u-3)*(c^2-2*c)+(u-3)*(u-2)^2*(c^3-3*c^2)

theorem Ghat_eq (u c : K) : Ghat u c=2*cut u c := by
  simp only [Ghat,q₀,q₁,q₂,cut]
  ring

/-- A zero active cubic coordinate at the fourth reverse site forces
the literal bidegree-(3,3) curve. -/
theorem cut_eq_zero {u c : K} (h₂ : (2:K)≠0) (hM : M u≠0)
    (read : M u*Ghat u c+Ehat u c*0=0) : cut u c=0 := by
  rw [mul_zero,add_zero,Ghat_eq,←mul_assoc] at read
  exact (mul_eq_zero.mp read).resolve_left (mul_ne_zero hM h₂)

/-- A reciprocal conic with nonzero coordinates cannot contain an
affine line with two independent coefficient vectors.  The variables
x,y,z are the relative slopes at a point with all three coordinates
nonzero. -/
theorem conic_slopes_equal {A B C x y z : K} (hA : A≠0) (hB : B≠0) (hC : C≠0)
    (h₀ : A+B+C=0) (h₁ : A*(y+z)+B*(x+z)+C*(x+y)=0)
    (h₂ : A*y*z+B*x*z+C*x*y=0) : x=z ∧ y=z := by
  have p : C*(x-z)*(y-z)=0 := by
    linear_combination h₂-z*h₁+z^2*h₀
  have hlin : A*(x-z)+B*(y-z)=0 := by
    linear_combination -h₁+(x+y)*h₀
  rcases (mul_eq_zero.mp p) with p | p
  · have xx := sub_eq_zero.mp ((mul_eq_zero.mp p).resolve_left hC)
    rw [xx,sub_self,mul_zero,zero_add] at hlin
    exact ⟨xx,sub_eq_zero.mp ((mul_eq_zero.mp hlin).resolve_left hB)⟩
  · have yy := sub_eq_zero.mp p
    rw [yy,sub_self,mul_zero,add_zero] at hlin
    exact ⟨sub_eq_zero.mp ((mul_eq_zero.mp hlin).resolve_left hA),yy⟩

end field

/-- Exact inverse of the four-by-four uniform moment form. -/
theorem hilbert_four_injective {a b c d : ℚ}
    (e₀ : a+b/2+c/3+d/4=0)
    (e₁ : a/2+b/3+c/4+d/5=0)
    (e₂ : a/3+b/4+c/5+d/6=0)
    (e₃ : a/4+b/5+c/6+d/7=0) : a=0 ∧ b=0 ∧ c=0 ∧ d=0 := by
  refine ⟨?_,?_,?_,?_⟩
  · linear_combination 16*e₀-120*e₁+240*e₂-140*e₃
  · linear_combination -120*e₀+1200*e₁-2700*e₂+1680*e₃
  · linear_combination 240*e₀-2700*e₁+6480*e₂-4200*e₃
  · linear_combination -140*e₀+1680*e₁-4200*e₂+2800*e₃

def rateVNumer (u : ℚ) : ℚ := 4*u^3-24*u^2+39*u-17
def leadingFactor (u : ℚ) : ℚ := 2*u^2-10*u+11

theorem rate_identity (u : ℚ) :
    M u*rateVNumer u+2*rateVNumer u-T u=
    2*(u-3)*(u-1)^2*leadingFactor u := by
  simp only [M,T,rateVNumer,leadingFactor]
  ring

theorem leading_ne (u : ℚ) : leadingFactor u≠0 := by
  intro e
  unfold leadingFactor at e
  have h3 : (2*u-5)^2=3 := by linear_combination 2*e
  have nat_no : ¬ IsSquare (3:ℕ) := by
    rintro ⟨m,h⟩
    by_cases b : 2≤m
    · have ge : 4≤m*m := Nat.mul_le_mul b b
      omega
    · have e' : m=0 ∨ m=1 := by omega
      rcases e' with rfl | rfl <;> norm_num at h
  exact ((Rat.isSquare_natCast_iff (n:=3)).not.mpr nat_no)
    ⟨2*u-5,by linear_combination -h3⟩

end RKResearch.Certified.SDIRKSevenDirtyVisibleZero
