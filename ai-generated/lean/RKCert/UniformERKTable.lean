module

public import RKCert.UniformERK
public import Mathlib.Data.ZMod.Basic

@[expose] public section

/-! # Regression checks for the uniform ERK lower-bound column

These are applications of the general theorem at the actual tableau input,
not a finite computation claiming to test unknown tableau entries.
-/
namespace RKCert

def uniformERKTable (i : Fin 20) : ℕ :=
  ([1,2,3,4,6,7,9,10,12,13,15,16,18,19,21,22,24,25,27,28] : List ℕ)[i.val]!

private theorem uniformERKTable_eq : ∀ i : Fin 20, uniformERKTable i =
    max (i.val+1) ((3*(i.val+1)+1)/2-2) := by decide

/-- Explicitly matches all twenty entries to the uniform ring theorem. -/
theorem uniform_erk_ring_through_twenty {R : Type*} [CommRing R] [Nontrivial R]
    {s : ℕ} (i : Fin 20) {A : Fin s → Fin s → R} {b : Fin s → R}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b (i.val+1)) : uniformERKTable i ≤ s := by
  rw [uniformERKTable_eq]
  exact uniform_erk_ring ha ho

/-- Odd-order boundary case: the fifth order rules out five stages, even
over this finite ring with zero divisors and without assumptions on b. -/
theorem zmod77_no_five_stage_order_five {A : Fin 5 → Fin 5 → ZMod 77} {b : Fin 5 → ZMod 77}
    (ha : StrictLower A) : ¬ HasTreeOrderAtLeast A b 5 := by
  intro ho
  let : Fact (1 < 77) := ⟨by decide⟩
  exact (by decide : ¬ max 5 ((3*5+1)/2-2) ≤ 5) (uniform_erk_ring ha ho)

/-- Odd endpoint at the top requested odd order, in an actual positive
characteristic field where 19! is invertible. -/
theorem zmod23_no_26_stage_order_nineteen
    {A : Fin 26 → Fin 26 → ZMod 23} {b : Fin 26 → ZMod 23}
    (ha : StrictLower A) : ¬ HasTreeOrderAtLeast A b 19 := by
  intro ho
  let : Fact (1 < 23) := ⟨by decide⟩
  exact (by decide : ¬ max 19 ((3*19+1)/2-2) ≤ 26) (uniform_erk_ring ha ho)

end RKCert
