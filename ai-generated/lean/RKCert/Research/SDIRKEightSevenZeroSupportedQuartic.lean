import Mathlib.Tactic.Ring.Basic

/-!
The division-free scalar part of the supported early-quartic argument.
The rooted flag, polynomial profile, and cardinal-moment ingress are
proved separately in the accompanying source note.
-/

namespace RKResearch.Certified.SDIRKEightSevenZeroSupportedQuartic

variable {R : Type*} [CommRing R]

def kappa (v : R) : R := 1+2*v-v^2
def ghostH (v : R) : R := v^3-4*v^2-v+2
def frontQ (v : R) : R := 4*v^3-12*v^2+3*v+2

/-- Two times v² times the normalized reflected P₄ moment of grade j. -/
def num (v ρ : R) (j : ℕ) : R :=
  kappa v - 2*(1+v)^j+ρ*(1+2*v)^j

def a₀ (v ρ : R) : R := num v ρ 0-num v ρ 1
def a₁ (v ρ : R) : R := 2*num v ρ 1-num v ρ 2
def c₀ (v ρ : R) : R := num v ρ 1-(1+2*v)*num v ρ 0
def c₁ (v ρ : R) : R := num v ρ 2-(1+2*v)*num v ρ 1

theorem arithmetic_quartic_determinant (v ρ : R) :
    2*a₀ v ρ*c₁ v ρ-a₁ v ρ*c₀ v ρ =
      2*v^2*(ρ*frontQ v-ghostH v) := by
  unfold a₀ a₁ c₀ c₁ num kappa ghostH frontQ
  ring1

/-- The two literal gap parameters have no common zero when 2 is a unit. -/
theorem ghost_front_bezout (v : R) :
    (676*v^2-1604*v-493)*ghostH v+
      (-169*v^2+570*v+525)*frontQ v = 64 := by
  unfold ghostH frontQ
  ring1

theorem no_live_arithmetic [IsDomain R]
    {v ρ ν κ₃ : R}
    (h₂ : (2:R)≠0) (hv : v≠0) (hk : kappa v≠0)
    (hp₀ : a₀ v ρ+ν*c₀ v ρ=0)
    (hp₁ : a₁ v ρ+2*ν*c₁ v ρ=0)
    (hCar : κ₃*ρ=kappa v)
    (hLit : ghostH v*κ₃=-(kappa v*frontQ v)) :
    False := by
  have det0 : 2*a₀ v ρ*c₁ v ρ-a₁ v ρ*c₀ v ρ=0 := by
    calc
      _ = 2*(a₀ v ρ+ν*c₀ v ρ)*c₁ v ρ -
          (a₁ v ρ+2*ν*c₁ v ρ)*c₀ v ρ := by ring1
      _ = _ := by rw [hp₀,hp₁]; ring1
  have hplus : ρ*frontQ v=ghostH v := by
    rw [arithmetic_quartic_determinant] at det0
    exact sub_eq_zero.mp
      ((mul_eq_zero.mp det0).resolve_left (mul_ne_zero h₂ (pow_ne_zero 2 hv)))
  have hm : kappa v*(ghostH v+ρ*frontQ v)=0 := by
    calc
      _ = ghostH v*(kappa v-κ₃*ρ)+ρ*(ghostH v*κ₃+kappa v*frontQ v) := by ring1
      _ = _ := by rw [hCar,hLit]; ring1
  have hH₂ : (2:R)*ghostH v=0 := by
    calc
      _ = ghostH v+ρ*frontQ v := by rw [hplus]; ring1
      _ = 0 := (mul_eq_zero.mp hm).resolve_left hk
  have hH := (mul_eq_zero.mp hH₂).resolve_left h₂
  have hρ : ρ≠0 := by
    intro h
    rw [h,mul_zero] at hCar
    exact hk hCar.symm
  have hQ : frontQ v=0 :=
    (mul_eq_zero.mp (hplus.trans hH)).resolve_left hρ
  have h64 : (64:R)≠0 := by
    have eq : (64:R)=(2:R)^6 := by ring1
    rw [eq]
    exact pow_ne_zero 6 h₂
  have bz := ghost_front_bezout v
  rw [hH,hQ,mul_zero,mul_zero,zero_add] at bz
  exact h64 bz.symm

end RKResearch.Certified.SDIRKEightSevenZeroSupportedQuartic
