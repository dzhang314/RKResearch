module

public import RKCert.Research.SDIRKSevenPairedClean
public import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Reflection-suffix Christoffel rational gates

The executable integer polynomial recurrence independently computes the two
rescaled discriminant residues. These lemmas give the scalar chronology,
the exceptional coefficients, and the ensuing primitive integer contradictions.
-/

namespace RKResearch.Certified.SDIRKSevenChristoffelReflection

theorem reflection_fourth_coefficients
    {M a₀ a₂ a₃ L₀ L₁ κ : ℚ}
    (h₀ : a₀=L₀+(M-2)*κ)
    (h₂ : a₂=L₀/2-2*L₁-5*κ)
    (h₃ : a₃=L₁/2+κ) :
    2*L₀+(5*M-4)*κ=5*a₀-6*a₂-24*a₃ ∧
    2*L₁+(4-M)*κ=2*a₂+12*a₃-a₀ := by
  constructor
  · linear_combination -5*h₀+6*h₂+24*h₃
  · linear_combination h₀-2*h₂-12*h₃

theorem reflection_pivot_degenerate {a₀ a₁ a₂ a₃ : ℚ}
    (opener : a₀+a₁+2*a₂+6*a₃=0)
    (slope : 2*a₂+12*a₃-a₀=0)
    (constant : 5*a₀-6*a₂-24*a₃=0) :
    a₀= -6*a₃ ∧ a₁=18*a₃ ∧ a₂= -9*a₃ := by
  refine ⟨?_,?_,?_⟩
  · linear_combination (3/2:ℚ)*slope+(1/2:ℚ)*constant
  · linear_combination opener-4*slope-constant
  · linear_combination (5/4:ℚ)*slope+(1/4:ℚ)*constant

theorem no_late_reflection_mass {x : ℚ} (h : x^3-9*x^2+18*x-6=0) : False := by
  apply SDIRKSevenPairedClean.no_star_opening (x:=x)
  simp only [SDIRKSevenPairedClean.starQ,SDIRKSevenPairedClean.starJ]
  linear_combination (1/3:ℚ)*h

private theorem five_dvd_of_square (s : ℤ) (h : (5:ℤ)∣s^2) : (5:ℤ)∣s := by
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd s 5).mp
  apply sq_eq_zero_iff.mp
  simpa only [Int.cast_pow] using (ZMod.intCast_zmod_eq_zero_iff_dvd (s^2) 5).mpr h

theorem five_odd_factor (k : ℕ) {s n : ℤ}
    (h : s^2=(5:ℤ)^(2*k+1)*n) : (n:ZMod 5)=0 := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd n 5).mpr
  induction k generalizing s with
  | zero =>
    have hd : (5:ℤ)∣s := five_dvd_of_square s ⟨n,by simpa using h⟩
    obtain ⟨r,rfl⟩ := hd
    refine ⟨r^2,?_⟩
    apply mul_left_cancel₀ (a:=(5:ℤ)) (by norm_num)
    norm_num at h
    linear_combination -h
  | succ k ih =>
    have hd : (5:ℤ)∣s :=
      five_dvd_of_square s ⟨5^(2*(k+1))*n,by rw [h,pow_succ]; ring⟩
    obtain ⟨r,rfl⟩ := hd
    apply ih (s:=r)
    apply mul_left_cancel₀ (a:=(5:ℤ)^2) (by norm_num)
    rw [show 2*(k+1)+1=2*k+1+2 by omega,pow_add] at h
    linear_combination h

def residueA (k : ZMod 5) : ZMod 5 := 3*k^4+4*k^3+2*k^2+k+3

theorem residueA_at_four : residueA 4=3 := by decide +kernel

theorem chart_A_not_square {s n : ℤ} {d f k : ZMod 5}
    (hd : d≠0) (hf : f≠0) (hk : k=4)
    (h : (n:ZMod 5)=d^36*f^18*residueA k)
    (sq : s^2=(5:ℤ)^7*n) : False := by
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have z := five_odd_factor 3 sq
  rw [h,hk,residueA_at_four] at z
  exact (mul_ne_zero (mul_ne_zero (pow_ne_zero 36 hd) (pow_ne_zero 18 hf))
    (by decide)) z

theorem chart_B_not_square {s n : ℤ} {d f : ZMod 5}
    (hd : d≠0) (hf : f≠0)
    (h : (n:ZMod 5)=2*d^22*f^18)
    (sq : s^2=(5:ℤ)^5*n) : False := by
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have z := five_odd_factor 2 sq
  rw [h] at z
  exact (mul_ne_zero (mul_ne_zero (by decide) (pow_ne_zero 22 hd))
    (pow_ne_zero 18 hf)) z

end RKResearch.Certified.SDIRKSevenChristoffelReflection
