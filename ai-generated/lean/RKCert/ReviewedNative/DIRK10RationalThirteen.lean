module

public import RKCert.ReviewedNative.DIRK10RationalThirteenGram
public import Mathlib.Algebra.Field.Rat
public import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Exact order 10 in 13 rational DIRK stages

The reviewed rooted-tree predicate holds for this literal coefficient
array over every commutative ring paying its common denominator.
The next bush violates the condition by a unit.
-/

namespace RKResearch.Certified.DIRK10RationalThirteen
open FiniteRootedTree
open scoped Matrix
set_option maxRecDepth 22000
set_option maxHeartbeats 0

variable {R : Type*} [CommRing R]

def A (d : R) : Matrix (Fin 13) (Fin 13) R :=
  d • M.map (Int.castRingHom R)

def b (d : R) : Fin 13 → R :=
  d • (Int.castRingHom R ∘ w)

theorem lower (d : R) : (A d).IsLowerTriangular := by
  change ∀ i j : Fin 13, i < j → A d i j = 0
  intro i j h
  change d * (M i j : R) = 0
  simp [M, h]

theorem rational_diagonals :
    A ((D : ℚ)⁻¹) 1 1 = 1 / 14 ∧ A ((D : ℚ)⁻¹) 2 2 = 13 / 108 := by
  decide +kernel

theorem order_ten (d : R) (hd : (D:R) * d = 1) : HasOrder 10 (A d) (b d) := by
  let f := Int.castRingHom R
  have hfd : f D * d = 1 := hd
  have hA : M.map f = f D • A d := by
    change M.map f = f D • (d • M.map f)
    rw [smul_smul, hfd, one_smul]
  have hb : f ∘ w = f D • b d := by
    change f ∘ w = f D • (d • (f ∘ w))
    rw [smul_smul, hfd, one_smul]
  have hu : IsUnit (f D) := IsUnit.of_mul_eq_one _ hd
  exact order_scaled f (A d) (b d) hA hb hu

private theorem clocks : M *ᵥ (1 : Fin 13 → ℤ) = c := by
  funext i
  exact (by decide +kernel : ∀ j : Fin 13, (M *ᵥ (1 : Fin 13 → ℤ)) j = c j) i

def bush11 : FiniteRootedTree := bushyTree 11

theorem bush_integer :
    (2488320:ℤ)*((bush11.factorial:ℤ)*(w ⬝ᵥ Φ bush11 M))=2488321*D^11 := by
  rw [bush11, factorial_bushyTree, Φ_bushyTree, clocks]
  decide +kernel

theorem bush_defect (d : R) (hd : (D:R) * d = 1) :
    (2488320:R)*((bush11.factorial:R)*(b d ⬝ᵥ Φ bush11 (A d))-1)=1 := by
  let f := Int.castRingHom R
  have hmap0 := congrArg f bush_integer
  change f (2488320*((bush11.factorial:ℤ)*(w ⬝ᵥ Φ bush11 M))) =
    f (2488321*D^11) at hmap0
  simp only [map_mul, map_pow, map_ofNat, map_natCast, RingHom.map_dotProduct,
    RKResearch.map_Φ] at hmap0
  have hs : ((bush11.order:ℕ)-1)=10 := by decide
  simp only [A, b, Φ_matrix_smul, hs, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  change _ = (1:R)
  calc
    _ = ((2488320:R)*((bush11.factorial:R)*((f ∘ w) ⬝ᵥ Φ bush11 (M.map f))))*d^11-2488320 := by ring
    _ = (1:R) := by
      rw [hmap0, mul_assoc, ←mul_pow]
      change (2488321:R)*((D:R)*d)^11-2488320 = (1:R)
      rw [hd]
      ring

theorem not_order_eleven [Nontrivial R] (d : R) (hd : (D:R) * d = 1) :
    ¬ HasOrder 11 (A d) (b d) := by
  intro h
  have horder : ((bush11.order:ℕ)≤11) := by decide
  have hfail := bush_defect d hd
  rw [h bush11 horder, sub_self, mul_zero] at hfail
  exact zero_ne_one hfail

theorem exists_exact_of_unit [Nontrivial R] (hD : IsUnit (D:R)) :
    ∃ (U : Matrix (Fin 13) (Fin 13) R) (z : Fin 13 → R),
      U.IsLowerTriangular ∧ HasOrder 10 U z ∧ ¬ HasOrder 11 U z := by
  obtain ⟨u,hu⟩ := hD
  let d : R := ↑(u⁻¹)
  have hd : (D:R)*d=1 := by rw [←hu]; exact u.mul_inv
  exact ⟨A d, b d, lower d, order_ten d hd, not_order_eleven d hd⟩

theorem exists_exact_charZero (K : Type*) [Field K] [CharZero K] :
    ∃ (U : Matrix (Fin 13) (Fin 13) K) (z : Fin 13 → K),
      U.IsLowerTriangular ∧ HasOrder 10 U z ∧ ¬ HasOrder 11 U z :=
  exists_exact_of_unit ((Int.cast_ne_zero.mpr (show D ≠ 0 by decide +kernel)).isUnit)

theorem exists_exact_rational :
    ∃ (U : Matrix (Fin 13) (Fin 13) ℚ) (z : Fin 13 → ℚ),
      U.IsLowerTriangular ∧ HasOrder 10 U z ∧ ¬ HasOrder 11 U z :=
  exists_exact_charZero ℚ

end RKResearch.Certified.DIRK10RationalThirteen
