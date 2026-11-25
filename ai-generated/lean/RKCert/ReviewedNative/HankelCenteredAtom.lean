module

public import RKCert.ReviewedNative.HankelLegendreIntData
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Basic

@[expose] public section

/-! # Finite, cleared raw-to-centered atom identity

The index still ranges through the same paid degrees 0,...,19.
A factorial form makes the closed integer calculation small; its
binomial interpretation is separately proved. -/
namespace RKResearch.Certified.Graded.HankelCenteredAtom

open HankelLegendreIntData

def rawAtom (j : ℕ) : ℤ := ((paidNat/(j+1) : ℕ) : ℤ)

def centeredCoeff (n j : ℕ) : ℤ :=
  ((n.descFactorial j / j.factorial : ℕ) : ℤ) * (2:ℤ)^j * (-1:ℤ)^(n-j)

theorem centeredCoeff_eq (n j : ℕ) :
    centeredCoeff n j = (n.choose j : ℤ) * (2:ℤ)^j * (-1:ℤ)^(n-j) := by
  rw [centeredCoeff, ← Nat.choose_eq_descFactorial_div_factorial]

def centeredPrefix (n : ℕ) : ℕ → ℤ
  | 0 => 0
  | k+1 => centeredPrefix n k + centeredCoeff n k * rawAtom k

set_option maxRecDepth 4096 in
theorem centeredAtoms : ∀ j : Fin 20, centeredPrefix j.val (j.val+1) = atom j.val := by
  decide +kernel

end RKResearch.Certified.Graded.HankelCenteredAtom
