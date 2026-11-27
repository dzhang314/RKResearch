module

public import RKCert.ReviewedNative.FiniteScaledOrderCheck
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

@[expose] public section

/-! # Six strict stages attain exact order five over every paid ring

A single literal tableau over ℤ[1/30] has the unit diagonal 1/4.
The sixth tall and bush discrepancies are 11/64 and -7/400; their
specified integer combination is one. Verification uses the reviewed
rooted-tree contract and no characteristic or locality assumption.
-/
namespace RKResearch.Certified.SDIRKFivePaidSix

open FiniteRootedTree
open scoped Matrix

def M : Matrix (Fin 6) (Fin 6) ℤ :=
  !![864000,0,0,0,0,0;
     -3456000,864000,0,0,0,0;
     -648000,-216000,864000,0,0,0;
     459000,153000,252000,864000,0,0;
     956448,180576,72576,0,864000,0;
     1164375,118125,0,1458000,-1012500,864000]

def w : Fin 6 → ℤ := ![0,0,448000,6912000,-8000000,4096000]
abbrev D : ℤ := 3456000
abbrev G : ℤ := 864000

private def paid (M : Matrix (Fin 6) (Fin 6) ℤ) (w : Fin 6 → ℤ) (t : FiniteRootedTree) : ℤ :=
  (t.factorial : ℤ) * (w ⬝ᵥ Φ t M)

private theorem numerator_condition {R : Type*} [CommRing R]
    (f : ℤ →+* R) {M : Matrix (Fin 6) (Fin 6) ℤ} {w : Fin 6 → ℤ}
    {A : Matrix (Fin 6) (Fin 6) R} {b : Fin 6 → R} {d : ℤ}
    (hA : M.map f = f d • A) (hb : f ∘ w = f d • b)
    (h : HasOrder 6 A b) (t : FiniteRootedTree) (ht : t.order = 6) :
    f (paid M w t) = (f d)^6 := by
  have hs := h t (by rw [ht]; decide)
  simp only [paid, map_mul, map_natCast, RingHom.map_dotProduct, map_Φ, hA, hb,
    Φ_matrix_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, ht]
  change (t.factorial : R) * ((f d)^5 * (f d * (b ⬝ᵥ Φ t A))) = (f d)^6
  linear_combination (norm := ring) ((f d)^5 * f d) * hs

private theorem undo_unit {R : Type*} [CommRing R] (u : Rˣ) (x : R) :
    (u : R) * (x * ((u⁻¹ : Rˣ) : R)) = x := by
  rw [mul_left_comm, Units.mul_inv, mul_one]

private theorem witness_from_scale {R : Type*} [CommRing R] [Nontrivial R]
    {M : Matrix (Fin 6) (Fin 6) ℤ} {w : Fin 6 → ℤ} {d g a b : ℤ}
    (hd : IsUnit ((Int.castRingHom R) d)) (hg : g ∣ d)
    (htri : M.IsLowerTriangular) (hdiag : ∀ i, M i i = g)
    (hcheck : checkScaledOrder (fun v => M *ᵥ v) (fun v => w ⬝ᵥ v) d d 5 = true)
    (hex : a * (paid M w (tallTree 6) - d^6) + b * (paid M w (bushyTree 6) - d^6) = d^6) :
    ∃ (A : Matrix (Fin 6) (Fin 6) R) (b : Fin 6 → R) (γ : R),
      A.IsLowerTriangular ∧ (∀ i, A i i = γ) ∧ IsUnit γ ∧
        HasOrder 5 A b ∧ ¬ HasOrder 6 A b := by
  let f := Int.castRingHom R
  let u := hd.unit
  let A : Matrix (Fin 6) (Fin 6) R :=
    Matrix.of fun i j => f (M i j) * ((u⁻¹ : Rˣ) : R)
  let b' : Fin 6 → R := fun i => f (w i) * ((u⁻¹ : Rˣ) : R)
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
private theorem checked :
    checkScaledOrder (fun v => M *ᵥ v) (fun v => w ⬝ᵥ v) D D 5 = true := by
  decide +kernel

private theorem two_discrepancies :
    128 * (paid M w (tallTree 6) - D^6) +
      1200 * (paid M w (bushyTree 6) - D^6) = D^6 := by
  decide +kernel

/-- No field or local-ring assumption; the sole unit hypothesis is
necessary for the existence of order five by the quadrature conditions. -/
theorem exists_exact_of_paid {R : Type*} [CommRing R] [Nontrivial R]
    (h30 : IsUnit (30 : R)) :
    ∃ (A : Matrix (Fin 6) (Fin 6) R) (b : Fin 6 → R) (γ : R),
      A.IsLowerTriangular ∧ (∀ i, A i i = γ) ∧ IsUnit γ ∧
        HasOrder 5 A b ∧ ¬ HasOrder 6 A b := by
  have hd : IsUnit ((Int.castRingHom R) D) := by
    apply isUnit_of_dvd_unit _ (h30.pow 10)
    refine ⟨(170859375 : R), ?_⟩
    simp only [D, map_ofNat]
    ring
  apply witness_from_scale hd (g := G) (by decide) _ _ checked two_discrepancies
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · decide +kernel

/-- The fifth tall-tree equation implies that 30 is invertible,
at every stage count and regardless of the tableau shape. -/
theorem paid_of_hasOrder {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
    {A : Matrix ι ι R} {b : ι → R} (ho : HasOrder 5 A b) : IsUnit (30 : R) := by
  have h120 : IsUnit (120 : R) := by
    apply IsUnit.of_mul_eq_one (b ⬝ᵥ Φ (tallTree 5) A)
    have ht := ho (tallTree 5) (by rw [order_tallTree]; decide)
    have hfact : ((tallTree 5).factorial : ℕ) = 120 := by decide +kernel
    simpa only [hfact, Nat.cast_ofNat] using ht
  exact isUnit_of_dvd_unit ⟨4, by ring⟩ h120

/-- Exact order-five existence at six stages is equivalent to the
necessary coefficient-ring condition for existence at any stage count. -/
theorem exists_exact_iff_paid {R : Type*} [CommRing R] [Nontrivial R] :
    (∃ (A : Matrix (Fin 6) (Fin 6) R) (b : Fin 6 → R) (γ : R),
      A.IsLowerTriangular ∧ (∀ i, A i i = γ) ∧ IsUnit γ ∧
        HasOrder 5 A b ∧ ¬ HasOrder 6 A b) ↔ IsUnit (30 : R) := by
  constructor
  · rintro ⟨A, b, γ, _, _, _, ho, _⟩
    exact paid_of_hasOrder ho
  · exact exists_exact_of_paid

end RKResearch.Certified.SDIRKFivePaidSix
