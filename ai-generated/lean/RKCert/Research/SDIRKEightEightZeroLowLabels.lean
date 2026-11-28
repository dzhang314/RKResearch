import Mathlib.Tactic.Ring.Basic

/-!
Paid scalar arithmetic for the exactly-eight-zero low-label exclusion.
The actual rooted flags and chronology remain separate from this module.
-/

namespace RKResearch.Certified.SDIRKEightEightZeroLowLabels

variable {R : Type*} [CommRing R]

def frontQ (v : R) : R := 4*v^3-12*v^2+3*v+2
def gapR (v : R) : R := 28*v^2-9*v-6
def rearSextic (v : R) : R :=
  8*v^6-44*v^5+22*v^4+97*v^3-55*v^2-13*v+6

theorem sextic_mod_front (v : R) :
    rearSextic v = (2*v^3-5*v^2-11*v-6)*frontQ v-3*gapR v := by
  unfold rearSextic frontQ gapR
  ring1

theorem front_gap_bezout (v : R) :
    (-2268*v-895)*frontQ v+(324*v^2-740*v-309)*gapR v=64 := by
  unfold frontQ gapR
  ring1

/-- In particular a live arithmetic third reflected residual cannot be
zero once the nonzero-second-row sextic has been extracted. -/
theorem no_zero_third_of_sextic [IsDomain R]
    {v : R} (h₂ : (2:R)≠0) (h₃ : (3:R)≠0)
    (hQ : frontQ v=0) (hS : rearSextic v=0) : False := by
  have hz : (3:R)*gapR v=0 := by
    have hh := sextic_mod_front v
    rw [hQ,hS,mul_zero,zero_sub] at hh
    exact neg_eq_zero.mp hh.symm
  have hR := (mul_eq_zero.mp hz).resolve_left h₃
  have h64 : (64:R)≠0 := by
    have e : (64:R)=(2:R)^6 := by ring1
    rw [e]
    exact pow_ne_zero 6 h₂
  have hh := front_gap_bezout v
  simp only [hQ,hR,mul_zero,zero_add] at hh
  exact h64 hh.symm

/-- The cleared prospective last label satisfies the quadratic gate
without a division by its ordinary first moment or by a weight. -/
theorem cleared_last_label {m₀ m₁ m₂ x c₀ c₁ c₂ : R}
    (h₀ : m₁=x*m₀) (h₁ : m₂=x*m₁)
    (hx : c₀+c₁*x+c₂*x^2=0) :
    m₀*m₂-m₁^2=0 ∧ c₀*m₀^2+c₁*m₁*m₀+c₂*m₁^2=0 := by
  constructor
  · rw [h₁,h₀]
    ring1
  · calc
      _ = (c₀+c₁*x+c₂*x^2)*m₀^2 := by rw [h₀]; ring1
      _ = 0 := by rw [hx,zero_mul]

end RKResearch.Certified.SDIRKEightEightZeroLowLabels
