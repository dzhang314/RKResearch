module

public import RKCert.ReviewedNative.RationalStrictSDIRKSevenStageSixUpper
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

public section

/-! # Uniform seven-stage strict SDIRK of exact order six

The integer numerator tableau of the existing rational construction transports
to any coefficient ring in which 6! is a unit. Unlike a seventh tall failure,
which can disappear modulo 71, the seventh bush has unit discrepancy.
-/

namespace RKResearch
open FiniteRootedTree
open scoped Matrix

/-- The paid tall tree at size six makes the factorial of six a unit,
including when the coefficient ring has zero divisors. -/
theorem HasOrder.sixFactorial_isUnit {R : Type*} [CommRing R] [Fintype ι]
    {A : Matrix ι ι R} {b : ι → R} (ho : HasOrder 6 A b) : IsUnit (720 : R) := by
  apply IsUnit.of_mul_eq_one (b ⬝ᵥ Φ (tallTree 6) A)
  have h := ho (tallTree 6) (by rw [order_tallTree]; decide)
  have hfact : ((tallTree 6).factorial : ℕ) = 720 := by decide +kernel
  simpa only [hfact, Nat.cast_ofNat] using h

namespace Certified.SDIRKSevenStageOrderSixRing
open Certified.RationalStrictSDIRKSevenStageSixUpper (AInt bInt)
variable {R : Type*} [CommRing R]

private theorem unitOfNatDvd {d m : ℕ} (h : d ∣ m) (hm : IsUnit (m : R)) :
    IsUnit (d : R) := by
  obtain ⟨e,he⟩ := h
  apply isUnit_of_dvd_unit _ hm
  exact ⟨(e : R), by simpa only [Nat.cast_mul] using congrArg ((↑) : ℕ → R) he⟩

private theorem denominators (h : IsUnit (720 : R)) :
    IsUnit (1536 : R) ∧ IsUnit (90 : R) := by
  have ha : IsUnit ((720^3 : ℕ) : R) := by simpa only [Nat.cast_pow, Nat.cast_ofNat] using h.pow 3
  exact ⟨unitOfNatDvd (d := 1536) (by decide) ha,
    unitOfNatDvd (d := 90) (by decide) ha⟩

private theorem numerator_triangular : AInt.IsLowerTriangular := by
  change ∀ i j : Fin 7, i < j → AInt i j = 0
  intro i j
  fin_cases i <;> fin_cases j <;> decide +kernel

private theorem numerator_diagonal (i : Fin 7) : AInt i i = 384 :=
  (by decide +kernel : ∀ i : Fin 7, AInt i i = 384) i

set_option maxHeartbeats 4000000 in
private theorem numerator_checked :
    checkScaledOrder (fun v => AInt *ᵥ v) (fun v => bInt ⬝ᵥ v) 1536 90 6 = true := by
  decide +kernel

private theorem numerator_bushy_seven :
    384 * (((bushyTree 7).factorial : ℤ) * (bInt ⬝ᵥ Φ (bushyTree 7) AInt)) =
      385 * (90 * (1536:ℤ)^6) := by
  rw [factorial_bushyTree, Φ_bushyTree]
  decide +kernel

/-- Every nonzero commutative ring with 6! a unit has an exact-order-six
strict SDIRK with seven stages, with common unit diagonal the inverse of 4. -/
theorem exists_exact [Nontrivial R] (h : IsUnit (720 : R)) :
    ∃ (A : Matrix (Fin 7) (Fin 7) R) (b : Fin 7 → R) (γ : R),
      A.IsLowerTriangular ∧ (∀ i, A i i = γ) ∧
      IsUnit γ ∧ (4 : R) * γ = 1 ∧ HasOrder 6 A b ∧ ¬ HasOrder 7 A b := by
  obtain ⟨hd,he⟩ := denominators h
  obtain ⟨d,hd'⟩ := hd
  obtain ⟨e,he'⟩ := he
  let f := Int.castRingHom R
  let A : Matrix (Fin 7) (Fin 7) R := Matrix.of fun i j => (↑d⁻¹ : R) * f (AInt i j)
  let b : Fin 7 → R := fun i => (↑e⁻¹ : R) * f (bInt i)
  let γ : R := (↑d⁻¹ : R) * 384
  have hAu : AInt.map f = f 1536 • A := by
    ext i j
    simp only [map_ofNat]
    change f (AInt i j) = (1536:R) * ((↑d⁻¹ : R) * f (AInt i j))
    rw [←hd', ←mul_assoc]
    simp
  have hbu : f ∘ bInt = f 90 • b := by
    funext i
    simp only [map_ofNat]
    change f (bInt i) = (90:R) * ((↑e⁻¹ : R) * f (bInt i))
    rw [←he', ←mul_assoc]
    simp
  have hd : IsUnit (f 1536) := by rw [map_ofNat, ←hd']; exact d.isUnit
  have he : IsUnit (f 90) := by rw [map_ofNat, ←he']; exact e.isUnit
  have h4 : (4 : R) * γ = 1 := by
    have hdi : (1536 : R) * (↑d⁻¹ : R) = 1 := by rw [←hd']; simp
    change (4 : R) * ((↑d⁻¹ : R) * 384) = 1
    linear_combination (norm := ring) hdi
  refine ⟨A,b,γ,?_,?_,IsUnit.of_mul_eq_one (4:R) ((mul_comm _ _).trans h4),h4,?_,?_⟩
  · intro i j hij
    change (↑d⁻¹:R) * f (AInt i j) = 0
    rw [numerator_triangular hij, map_zero, mul_zero]
  · intro i
    change (↑d⁻¹:R) * f (AInt i i) = γ
    rw [numerator_diagonal, map_ofNat]
  · exact hasOrder_of_scaled_check f (fun _ => rfl) (fun _ => rfl)
      hAu hbu hd he numerator_checked
  · intro h7
    let t := bushyTree 7
    have ht : (t.order : ℕ) = 7 := by simp [t,order_bushyTree]
    have hpaid : (t.factorial : R) * (b ⬝ᵥ Φ t A) = 1 := h7 t (by rw [ht])
    have hn : f ((t.factorial : ℤ) * (bInt ⬝ᵥ Φ t AInt)) =
        (90 : R) * (1536 : R)^6 := by
      simp only [map_mul, map_natCast, RingHom.map_dotProduct, RKResearch.map_Φ,
        hAu, hbu, Φ_matrix_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, ht, map_ofNat]
      change (t.factorial : R) * ((1536:R)^6 * ((90:R) * (b ⬝ᵥ Φ t A))) = _
      linear_combination (norm := ring) ((90:R)*(1536:R)^6) * hpaid
    have hb : f (384 * ((t.factorial : ℤ) * (bInt ⬝ᵥ Φ t AInt))) =
        f (385 * (90 * (1536:ℤ)^6)) := congrArg f numerator_bushy_seven
    rw [map_mul, hn] at hb
    simp only [map_mul, map_pow, map_ofNat] at hb
    have hu : IsUnit ((90:R) * (1536:R)^6) := by
      simpa only [map_ofNat] using he.mul (hd.pow 6)
    exact hu.ne_zero (by linear_combination (norm := ring) -hb)

end Certified.SDIRKSevenStageOrderSixRing
end RKResearch
