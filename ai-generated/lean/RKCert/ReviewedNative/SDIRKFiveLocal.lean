module

public import RKCert.ReviewedNative.FiniteScaledOrderCheck
public import RKCert.ReviewedNative.NonsingularDIRKStageFloor
public import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases

@[expose] public section

/-! # Optimal exact strict SDIRK order five over paid local rings

Two exact rational five-stage witnesses have scales with gcd 324000,
a unit whenever 30 is. At least one scale is a unit in a local ring.
All rooted-tree verification is over the integer numerators; no
characteristic, reducedness or order assumptions are needed.
-/
namespace RKResearch.Certified.SDIRKFiveLocal

open FiniteRootedTree
open scoped Matrix

def M1 : Matrix (Fin 5) (Fin 5) ℤ :=
  !![4176902359476000,0,0,0,0;
     -2278310377896000,4176902359476000,0,0,0;
     21470718438865080,-18964577023179480,4176902359476000,0,0;
     -212798619954906216,122045027587972456,93259733782619360,4176902359476000,0;
     7854392480319000,-11190533495295000,-757559764500000,-83201580000000,4176902359476000]

def w1 : Fin 5 → ℤ := ![908863013404500,2696385689818700,-36251199875000,7475141953125,600429714174675]

abbrev D1 : ℤ := 4176902359476000
abbrev G1 : ℤ := 4176902359476000

def M2 : Matrix (Fin 5) (Fin 5) ℤ :=
  !![35070986340000,0,0,0,0;
     -210425918040000,35070986340000,0,0,0;
     44596718758800,18531056653200,35070986340000,0,0;
     35555723657987,-159822781197,27731874535210,35070986340000,0;
     55594007976000,-1438809696000,21209654400000,-5222880000000,35070986340000]

def w2 : Fin 5 → ℤ := ![81399326320000,99917340000,14001770000000,-130572000000000,175354931700000]

abbrev D2 : ℤ := 140283945360000
abbrev G2 : ℤ := 35070986340000

private def paid (M : Matrix (Fin 5) (Fin 5) ℤ) (w : Fin 5 → ℤ) (t : FiniteRootedTree) : ℤ :=
  (t.factorial : ℤ) * (w ⬝ᵥ Φ t M)

private theorem numerator_condition {R : Type*} [CommRing R]
    (f : ℤ →+* R) {M : Matrix (Fin 5) (Fin 5) ℤ} {w : Fin 5 → ℤ}
    {A : Matrix (Fin 5) (Fin 5) R} {b : Fin 5 → R} {d : ℤ}
    (hA : M.map f = f d • A) (hb : f ∘ w = f d • b)
    (h : HasOrder 6 A b) (t : FiniteRootedTree) (ht : t.order = 6) :
    f (paid M w t) = (f d)^6 := by
  have hs := h t (by rw [ht]; decide)
  simp only [paid, map_mul, map_natCast, RingHom.map_dotProduct, map_Φ, hA, hb,
    Φ_matrix_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, ht]
  change (t.factorial : R) * ((f d)^5 * (f d * (b ⬝ᵥ Φ t A))) = (f d)^6
  rw [show (6 : ℕ) = 5+1 by decide, pow_succ]
  linear_combination (norm := ring) ((f d)^5 * f d) * hs

private theorem undo_unit {R : Type*} [CommRing R] (u : Rˣ) (x : R) :
    (u : R) * (x * ((u⁻¹ : Rˣ) : R)) = x := by
  rw [mul_left_comm, Units.mul_inv, mul_one]

private theorem witness_from_scale {R : Type*} [CommRing R] [Nontrivial R]
    {M : Matrix (Fin 5) (Fin 5) ℤ} {w : Fin 5 → ℤ} {d g a b : ℤ}
    (hd : IsUnit ((Int.castRingHom R) d)) (hg : g ∣ d)
    (htri : M.IsLowerTriangular) (hdiag : ∀ i, M i i = g)
    (hcheck : checkScaledOrder (fun v => M *ᵥ v) (fun v => w ⬝ᵥ v) d d 5 = true)
    (hex : a * (paid M w (tallTree 6) - d^6) + b * (paid M w (bushyTree 6) - d^6) = d^6) :
    ∃ (A : Matrix (Fin 5) (Fin 5) R) (b : Fin 5 → R) (γ : R),
      A.IsLowerTriangular ∧ (∀ i, A i i = γ) ∧ IsUnit γ ∧
        HasOrder 5 A b ∧ ¬ HasOrder 6 A b := by
  let f := Int.castRingHom R
  let u := hd.unit
  let A : Matrix (Fin 5) (Fin 5) R :=
    Matrix.of fun i j => f (M i j) * ((u⁻¹ : Rˣ) : R)
  let b' : Fin 5 → R := fun i => f (w i) * ((u⁻¹ : Rˣ) : R)
  let γ : R := f g * ((u⁻¹ : Rˣ) : R)
  have hA : M.map f = f d • A := by
    funext i j
    change f (M i j) = f d * (f (M i j) * ((u⁻¹ : Rˣ) : R))
    rw [← hd.unit_spec]
    exact (undo_unit u _).symm
  have hb : f ∘ w = f d • b' := by
    funext i
    change f (w i) = f d * (f (w i) * ((u⁻¹ : Rˣ) : R))
    rw [← hd.unit_spec]
    exact (undo_unit u _).symm
  have hg' : IsUnit (f g) := isUnit_of_dvd_unit (map_dvd f hg) hd
  refine ⟨A, b', γ, ?_, ?_, hg'.mul (u⁻¹).isUnit, ?_, ?_⟩
  · intro i j hij
    change f (M i j) * ((u⁻¹ : Rˣ) : R) = 0
    rw [htri hij, map_zero, zero_mul]
  · intro i
    change f (M i i) * ((u⁻¹ : Rˣ) : R) = γ
    rw [hdiag]
  · exact hasOrder_of_scaled_check f (fun _ => rfl) (fun _ => rfl) hA hb hd hd hcheck
  · intro h6
    have ht := numerator_condition f hA hb h6 (tallTree 6) (by rw [order_tallTree])
    have hb' := numerator_condition f hA hb h6 (bushyTree 6) (by rw [order_bushyTree])
    have h := congrArg f hex
    simp only [map_add, map_sub, map_mul, map_pow, ht, hb', sub_self, mul_zero, zero_add] at h
    exact (hd.pow 6).ne_zero h.symm

set_option maxHeartbeats 4000000 in
private theorem checked1 :
    checkScaledOrder (fun v => M1 *ᵥ v) (fun v => w1 ⬝ᵥ v) D1 D1 5 = true := by
  decide +kernel

set_option maxHeartbeats 4000000 in
private theorem checked2 :
    checkScaledOrder (fun v => M2 *ᵥ v) (fun v => w2 ⬝ᵥ v) D2 D2 5 = true := by
  decide +kernel

private theorem exclusion1 :
    (-5) * (paid M1 w1 (tallTree 6) - D1^6) +
      (14300) * (paid M1 w1 (bushyTree 6) - D1^6) = D1^6 := by
  decide +kernel

private theorem exclusion2 :
    (-8832) * (paid M2 w2 (tallTree 6) - D2^6) +
      (-22400) * (paid M2 w2 (bushyTree 6) - D2^6) = D2^6 := by
  decide +kernel

variable {R : Type*} [CommRing R]

theorem exact_five_of_scales [Nontrivial R] (h : IsUnit ((D1 : ℤ) : R) ∨ IsUnit ((D2 : ℤ) : R)) :
    ∃ (A : Matrix (Fin 5) (Fin 5) R) (b : Fin 5 → R) (γ : R),
      A.IsLowerTriangular ∧ (∀ i, A i i = γ) ∧ IsUnit γ ∧
        HasOrder 5 A b ∧ ¬ HasOrder 6 A b := by
  rcases h with h | h
  · apply witness_from_scale h (g := G1) (by decide) _ _ checked1 exclusion1
    · intro i j
      fin_cases i <;> fin_cases j <;> decide +kernel
    · decide +kernel
  · apply witness_from_scale h (g := G2) (by decide) _ _ checked2 exclusion2
    · intro i j
      fin_cases i <;> fin_cases j <;> decide +kernel
    · decide +kernel

private theorem unit324000 (h30 : IsUnit (30 : R)) : IsUnit (324000 : R) := by
  apply isUnit_of_dvd_unit _ (h30.pow 5)
  refine ⟨75, ?_⟩
  ring

/-- The two integer scale charts cover every local ring in which 30 is
a unit, including all admissible fields and local rings with nilpotents. -/
theorem exists_exact_of_paid [IsLocalRing R] (h30 : IsUnit (30 : R)) :
    ∃ (A : Matrix (Fin 5) (Fin 5) R) (b : Fin 5 → R) (γ : R),
      A.IsLowerTriangular ∧ (∀ i, A i i = γ) ∧ IsUnit γ ∧
        HasOrder 5 A b ∧ ¬ HasOrder 6 A b := by
  let f := Int.castRingHom R
  have hz : (134909209 : ℤ) * D1 + (-4016871581 : ℤ) * D2 = 324000 := by decide +kernel
  have h := congrArg f hz
  simp only [map_add, map_mul, map_neg, map_ofNat] at h
  have hu : IsUnit ((134909209 : R) * ((D1 : ℤ) : R) +
      -(4016871581 : R) * ((D2 : ℤ) : R)) := by
    simp only [D1, D2, Int.cast_ofNat]
    rw [h]
    exact unit324000 h30
  apply exact_five_of_scales
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hu with ha | hb
  · exact Or.inl (isUnit_of_mul_isUnit_right ha)
  · exact Or.inr (isUnit_of_mul_isUnit_right hb)

/-- Over a paid local coefficient ring, five stages really are minimal. -/
theorem least_of_paid [IsLocalRing R] (h30 : IsUnit (30 : R)) :
    IsLeast {s : ℕ | ∃ (A : Matrix (Fin s) (Fin s) R) (b : Fin s → R) (γ : R),
      A.IsLowerTriangular ∧ (∀ i, A i i = γ) ∧ IsUnit γ ∧ HasOrder 5 A b} 5 := by
  obtain ⟨A,b,γ,ht,hg,hu,ho,-⟩ := exists_exact_of_paid h30
  refine ⟨⟨A,b,γ,ht,hg,hu,ho⟩, ?_⟩
  rintro s ⟨A,b,γ,ht,hg,-,ho⟩
  exact ho.common_diagonal_order_five_stages ht hg

end RKResearch.Certified.SDIRKFiveLocal
