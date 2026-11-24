module

public import RKCert.DirkGradeSix
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.ZMod.Basic

@[expose] public section
namespace RKCert.DIRKGradeSixRegression

/-- The theorem is about the original array, not an ordered-field transfer. -/
theorem no_complex_order13_s16 {A : Fin 16 → Fin 16 → ℂ} {b : Fin 16 → ℂ}
    (ha : ∀ i j : Fin 16, i.val<j.val → A i j=0)
    (ho : HasTreeOrderAtLeast A b 13) : False :=
  (by decide : ¬17≤16) (Paired.dirk_order13_charZero_field ha ho (by decide))

/-- A coefficient ring of characteristic zero may still have nonzero torsion
and nilpotents. No field or torsion-free hypothesis leaks into order twelve. -/
theorem no_charZero_torsion_order12_s14
    {A : Fin 14 → Fin 14 → ℚ × ZMod 529} {b : Fin 14 → ℚ × ZMod 529}
    (ha : ∀ i j : Fin 14, i.val<j.val → A i j=0)
    (ho : HasTreeOrderAtLeast A b 12) : False :=
  (by decide : ¬15≤14) (dirk_order12_charZero_ring ha ho (by decide))

/-- The uniform nontrivial ring table was not promoted to characteristic
zero: the older arbitrary-characteristic floor still applies separately. -/
theorem check_uniform_p13 {R : Type*} [CommRing R] [Nontrivial R]
    {s : ℕ} {A : Fin s → Fin s → R} {b : Fin s → R}
    (ha : ∀ i j : Fin s, i.val<j.val → A i j=0)
    (ho : HasTreeOrderAtLeast A b 13) : 16≤s := by
  exact dirkRingFloor_le_stages ha ho

end RKCert.DIRKGradeSixRegression
