module

public import RKCert.ReviewedNative.FiniteOrderCheck
public import RKResearch.ERK
public import Mathlib.Data.ZMod.Basic

@[expose] public section

/-!
# An eleven-stage explicit order-eight tableau in characteristic 41

The literal coefficients are the Cooper–Verner radical tableau specialized
at the root 12 of (X^2-21) in `ZMod 41`. The order certificate below is
checked directly, independent of the change-of-coefficients argument.
-/

namespace RKResearch.Certified.ERK8Characteristic41

open FiniteRootedTree
open scoped Matrix

def rows : Array (Array (ZMod 41)) :=
  #[
    #[], #[21], #[31,31], #[6,30,31], #[20,0,21,26],
    #[40,0,17,17,29], #[22,0,33,25,34,25],
    #[3,0,0,0,3,19,32], #[9,0,0,0,28,3,16,6],
    #[3,0,0,0,32,13,31,30,40], #[0,0,0,0,34,14,17,13,9,37]]

def A : Matrix (Fin 11) (Fin 11) (ZMod 41) :=
  Matrix.of fun i j => if j < i then rows[i.val]![j.val]! else 0

def b (i : Fin 11) : ZMod 41 :=
  (#[39,0,0,0,0,0,0,21,4,21,39] : Array (ZMod 41))[i.val]!

theorem strictlyLower : ERK A := by
  intro i j h
  change (if j < i then rows[i.val]![j.val]! else 0) = 0
  simp [Fin.not_lt.mpr h]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem order_eight : HasOrder 8 A b := by
  apply (checkOrder_iff A b 8).mp
  decide +kernel

set_option maxHeartbeats 0 in
theorem ninth_bush_scaled :
    (bushyTree 9).factorial * (b ⬝ᵥ Φ (bushyTree 9) A) = (24 : ZMod 41) := by
  rw [factorial_bushyTree, Φ_bushyTree]
  decide +kernel

theorem not_order_nine : ¬ HasOrder 9 A b := by
  intro h
  have ht := h (bushyTree 9) (by rw [order_bushyTree]; decide)
  have he := ninth_bush_scaled
  rw [ht] at he
  exact (by decide +kernel : (1 : ZMod 41) ≠ 24) he

/-- The specialized tableau transfers to every nontrivial commutative
ring of characteristic 41, without an order or field hypothesis. -/
theorem exists_exact_order_eight (R : Type*) [CommRing R] [CharP R 41] [Nontrivial R] :
    ∃ (T : Matrix (Fin 11) (Fin 11) R) (w : Fin 11 → R),
      ERK T ∧ HasOrder 8 T w ∧ ¬ HasOrder 9 T w := by
  let f : ZMod 41 →+* R := ZMod.castHom (dvd_refl 41) R
  refine ⟨A.map f, f ∘ b, ?_, order_eight.map f, ?_⟩
  · intro i j h
    change f (A i j) = 0
    rw [strictlyLower h, map_zero]
  · intro h
    apply not_order_nine
    exact (hasOrder_map_iff (f := f) (ZMod.castHom_injective R)).mp h

end RKResearch.Certified.ERK8Characteristic41

#print axioms RKResearch.Certified.ERK8Characteristic41.order_eight

#print axioms RKResearch.Certified.ERK8Characteristic41.exists_exact_order_eight
