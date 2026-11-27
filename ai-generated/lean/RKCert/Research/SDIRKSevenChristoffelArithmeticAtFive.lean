module

public import RKCert.Research.SDIRKSevenChristoffelReflection
public import Mathlib.Algebra.Field.ZMod

@[expose] public section

/-! # Arithmetic suffix with penultimate reflected clock zero modulo five -/

namespace RKResearch.Certified.SDIRKSevenChristoffelArithmeticAtFive

open SDIRKSevenChristoffelReflection

def lateHom {R : Type*} [CommRing R] (u a d : R) : R :=
  let K := (u-3)*(u-2)^2
  let J := (u-3)*(u-1)*(2*u-3)
  let V := (u-2)*(u-1)^2
  2*K*a^3-6*(K+J)*a^2*d+12*(V+J)*a*d^2-12*V*d^3

theorem late_rootless : ∀ a d : ZMod 5,
    (a≠0 ∨ d≠0) → lateHom 0 a d≠0 := by decide +kernel

theorem chart_A_not_square {s n : ℤ} {d f g : ZMod 5}
    (hd : d≠0) (hf : f≠0) (hg : g≠0)
    (h : (n:ZMod 5)=2*d^34*f^36*g^18)
    (sq : s^2=(5:ℤ)^7*n) : False := by
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have z := five_odd_factor 3 sq
  rw [h] at z
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by decide) (pow_ne_zero 34 hd))
    (pow_ne_zero 36 hf)) (pow_ne_zero 18 hg)) z

theorem chart_B_not_square {s n : ℤ} {d f g : ZMod 5}
    (hd : d≠0) (hf : f≠0) (hg : g≠0)
    (h : (n:ZMod 5)=3*d^34*f^22*g^18)
    (sq : s^2=(5:ℤ)^5*n) : False := by
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have z := five_odd_factor 2 sq
  rw [h] at z
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by decide) (pow_ne_zero 34 hd))
    (pow_ne_zero 22 hf)) (pow_ne_zero 18 hg)) z

end RKResearch.Certified.SDIRKSevenChristoffelArithmeticAtFive
