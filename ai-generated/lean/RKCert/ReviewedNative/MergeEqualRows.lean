module
public import RKResearch.OrderConditions
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-! # Native chronological contraction of two literally identical rows -/
namespace RKResearch.Certified.Graded
open RKResearch FiniteRootedTree
open scoped Matrix FiniteRootedTree

variable {R : Type*} [CommSemiring R] {n p : ℕ}

/-- Retain all columns except `j`, moving its coefficient onto the
retained representative `r`. -/
def mergeCoefficient (j : Fin (n+1)) (r : Fin n) (w : Fin (n+1) → R) : Fin n → R :=
  fun k => w (j.succAbove k) + if k = r then w j else 0

theorem sum_merge_coefficient (j : Fin (n+1)) (r : Fin n)
    (w v : Fin (n+1) → R) (hv : v j = v (j.succAbove r)) :
    (∑ k : Fin n, mergeCoefficient j r w k * v (j.succAbove k)) = ∑ k, w k * v k := by
  simp only [mergeCoefficient, add_mul, Finset.sum_add_distrib]
  rw [Fin.sum_univ_succAbove _ j, add_comm]
  congr 1
  rw [Finset.sum_eq_single r]
  · simp [hv]
  · intro k _ hk
    simp [hk]
  · simp

theorem phi_equal_incoming_rows {A : Matrix (Fin n) (Fin n) R} {i j : Fin n}
    (he : ∀ k, A i k = A j k) (t : FiniteRootedTree) :
    Φ t A i = Φ t A j := by
  induction t with
  | leaf => rfl
  | butcherProduct u v hu _ =>
    simp only [Φ, Pi.mul_apply, hu, Matrix.mulVec, dotProduct, he]

/-- Contract a literal duplicate into an earlier row, preserving strict
triangularity and every human-reviewed elementary weight including outputs. -/
theorem exists_merge_equal_rows {A : Matrix (Fin (n+1)) (Fin (n+1)) R}
    {b : Fin (n+1) → R} (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder p A b)
    {i j : Fin (n+1)} (hij : i < j) (he : ∀ k, A i k = A j k) :
    ∃ (B : Matrix (Fin n) (Fin n) R) (c : Fin n → R),
      (∀ i j, i ≤ j → B i j = 0) ∧ HasOrder p B c := by
  obtain ⟨r,hr⟩ := Fin.exists_succAbove_eq (ne_of_lt hij)
  let B : Matrix (Fin n) (Fin n) R :=
    fun a => mergeCoefficient j r (A (j.succAbove a))
  have hB (x y : Fin n) (hxy : x ≤ y) : B x y = 0 := by
    have h := (Fin.succAboveOrderEmb j).monotone hxy
    change j.succAbove x ≤ j.succAbove y at h
    by_cases hh : y = r
    · subst y
      have hi' : j.succAbove x ≤ i := hr ▸ h
      simp [B,mergeCoefficient,ha _ _ h,ha _ _ (hi'.trans hij.le)]
    · simp [B,mergeCoefficient,ha _ _ h,hh]
  have hPhi (t : FiniteRootedTree) (k : Fin n) :
      Φ t B k = Φ t A (j.succAbove k) := by
    induction t generalizing k with
    | leaf => rfl
    | butcherProduct u v hu hv =>
      simp only [Φ,Pi.mul_apply,hu,Matrix.mulVec,dotProduct,hv]
      congr 1
      exact sum_merge_coefficient j r (A (j.succAbove k)) (Φ v A)
        (by rw [hr]; exact (phi_equal_incoming_rows he v).symm)
  refine ⟨B,mergeCoefficient j r b,hB,?_⟩
  intro t ht
  have mass : mergeCoefficient j r b ⬝ᵥ Φ t B = b ⬝ᵥ Φ t A := by
    simp only [dotProduct,hPhi]
    exact sum_merge_coefficient j r b (Φ t A) (by rw [hr]; exact (phi_equal_incoming_rows he t).symm)
  rw [mass]
  exact ho t ht

end RKResearch.Certified.Graded
