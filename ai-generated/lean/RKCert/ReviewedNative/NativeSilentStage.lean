module

public import RKResearch.OrderConditions
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-! # Delete one output-silent physical stage with an identically zero outgoing column

No derivative equality with another stage is needed: the column is
absent from every kept tree computation and from the output. -/
namespace RKResearch.Certified.Graded
open RKResearch FiniteRootedTree
open scoped Matrix FiniteRootedTree

variable {R : Type*} [CommSemiring R] {n p : ℕ}

private theorem sum_delete_dead (i : Fin (n+1)) (w v : Fin (n+1)→R) (dead : w i=0) :
    (∑ k : Fin n,w (i.succAbove k)*v (i.succAbove k))=∑ k,w k*v k := by
  rw [Fin.sum_univ_succAbove _ i]
  simp only [dead,zero_mul,zero_add,add_zero]

theorem delete_silent_stage {A : Matrix (Fin (n+1)) (Fin (n+1)) R}
    {b : Fin (n+1)→R} (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder p A b)
    (i : Fin (n+1)) (dead : b i=0) (out : ∀j,A j i=0) :
    (∀ j k : Fin n,j≤k → A (i.succAbove j) (i.succAbove k)=0) ∧
    HasOrder p (A.submatrix i.succAbove i.succAbove) (fun k=>b (i.succAbove k)) := by
  let B := A.submatrix i.succAbove i.succAbove
  refine ⟨fun j k h=>ha _ _ ((Fin.succAboveOrderEmb i).monotone h),?_⟩
  have same (t : FiniteRootedTree) (k : Fin n) : Φ t B k=Φ t A (i.succAbove k) := by
    induction t generalizing k with
    | leaf => rfl
    | butcherProduct u v hu hv =>
      simp only [Φ,Pi.mul_apply,hu,Matrix.mulVec,dotProduct,hv]
      congr 1
      exact sum_delete_dead i (A (i.succAbove k)) (Φ v A) (out _)
  intro t ht
  have mass : (fun k=>b (i.succAbove k)) ⬝ᵥ Φ t B = b ⬝ᵥ Φ t A := by
    simp only [dotProduct,same]
    exact sum_delete_dead i b (Φ t A) dead
  change (t.factorial:R)*((fun k=>b (i.succAbove k)) ⬝ᵥ Φ t B)=1
  rw [mass]
  exact ho t ht

end RKResearch.Certified.Graded
