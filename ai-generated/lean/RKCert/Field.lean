module

public import RKCert.Tree
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.CharZero.Defs

@[expose] public section

/-! # Equivalence with the usual order conditions over a characteristic-zero field -/

namespace RKCert

variable {K : Type*} [Field K] [CharZero K] {s : ℕ}

/-- Clearing tree denominators does not alter any order condition in characteristic zero. -/
theorem hasTreeOrderAtLeast_iff_inverse (A : Fin s → Fin s → K) (b : Fin s → K) (p : ℕ) :
    HasTreeOrderAtLeast A b p ↔
      ∀ t : Tree, t.order ≤ p → weight A b t = (t.density : K)⁻¹ := by
  have hden (t : Tree) : (t.density : K) ≠ 0 := Nat.cast_ne_zero.mpr t.density_pos.ne'
  constructor
  · intro h t ht
    calc
      weight A b t = (t.density : K)⁻¹ * ((t.density : K) * weight A b t) := by
        rw [← mul_assoc, inv_mul_cancel₀ (hden t), one_mul]
      _ = (t.density : K)⁻¹ := by rw [h t ht, mul_one]
  · intro h t ht
    rw [h t ht, mul_inv_cancel₀ (hden t)]

end RKCert
