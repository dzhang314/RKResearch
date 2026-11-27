module

public import RKCert.ReviewedNative.FastCausalFold

@[expose] public section

/-! Structural reduction of physical checks to the actual deleted copy rows. -/

namespace RKResearch.Certified.CausalStageMerge

open TwoOrderMomentTail
open scoped Matrix

theorem eq_of_actual_copies {old copies fresh : ℕ} {R : Type*}
    (donors : Fin copies → Fin old)
    (V : Matrix (Fin (old+copies+fresh)) (Fin (old+copies+fresh)) R)
    (h : ∀ (k : Fin copies) (j : Fin (old+copies+fresh)),
      V (copyIndex old fresh k) j = V (keepHead old copies fresh (donorLift fresh (donors k))) j) :
    ∀ i j, V i j = V (keepHead old copies fresh (redirectHead donors i)) j := by
  intro i j
  obtain ⟨i, rfl⟩ := (splitCopyEquiv old copies fresh).surjective i
  cases i with
  | inl i =>
    change V (keepHead old copies fresh i) j =
      V (keepHead old copies fresh (redirectHead donors (keepHead old copies fresh i))) j
    rw [redirect_keepHead]
  | inr i =>
    change V (copyIndex old fresh i) j =
      V (keepHead old copies fresh (redirectHead donors (copyIndex old fresh i))) j
    rw [redirect_copy]
    exact h i j

section Shape
variable {old fresh : ℕ} {K : Type*} [CommSemiring K]

/-- Actual joined chronological matrix. This is the standard sum-index
block laid out with the old prefix first. -/
def chronological (A : Matrix (Fin old) (Fin old) K)
    (U : Matrix (Fin fresh) (Fin old) K) (B : Matrix (Fin fresh) (Fin fresh) K) :
    Matrix (Fin (old+fresh)) (Fin (old+fresh)) K :=
  shifted finSumFinEquiv (Matrix.fromBlocks A 0 U B)

theorem chronological_lower
    {A : Matrix (Fin old) (Fin old) K} {U : Matrix (Fin fresh) (Fin old) K}
    {B : Matrix (Fin fresh) (Fin fresh) K}
    (hA : A.IsLowerTriangular) (hB : B.IsLowerTriangular) :
    (chronological A U B).IsLowerTriangular := by
  change ∀ ⦃i j : Fin (old+fresh)⦄, i < j → chronological A U B i j = 0
  intro i j hij
  have hv : i.val < j.val := hij
  let e : Fin old ⊕ Fin fresh ≃ Fin (old+fresh) := finSumFinEquiv
  obtain ⟨i', rfl⟩ := e.surjective i
  obtain ⟨j', rfl⟩ := e.surjective j
  change Matrix.fromBlocks A 0 U B (e.symm (e i')) (e.symm (e j')) = 0
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  cases i' with
  | inl a =>
    cases j' with
    | inl b =>
      have hab : a.val < b.val := by simpa [e,finSumFinEquiv_apply_left] using hv
      exact hA (show a < b from hab)
    | inr b => rfl
  | inr a =>
    cases j' with
    | inl b =>
      have h := b.isLt
      simp only [e,finSumFinEquiv_apply_left,finSumFinEquiv_apply_right,Fin.val_natAdd,Fin.val_castAdd] at hv
      omega
    | inr b =>
      simp only [e,finSumFinEquiv_apply_right,Fin.val_natAdd] at hv
      exact hB (show a < b from by change a.val < b.val; omega)

theorem chronological_diagonal
    {A : Matrix (Fin old) (Fin old) K} {U : Matrix (Fin fresh) (Fin old) K}
    {B : Matrix (Fin fresh) (Fin fresh) K} (d : K)
    (hA : ∀ i, A i i = d) (hB : ∀ i, B i i = d) :
    ∀ i, chronological A U B i i = d := by
  intro i
  let e : Fin old ⊕ Fin fresh ≃ Fin (old+fresh) := finSumFinEquiv
  obtain ⟨i, rfl⟩ := e.surjective i
  change Matrix.fromBlocks A 0 U B (e.symm (e i)) (e.symm (e i)) = d
  rw [Equiv.symm_apply_apply]
  cases i with
  | inl i => exact hA i
  | inr i => exact hB i

theorem strict_diag_reassembly
    {I R : Type*} [LinearOrder I] [AddZeroClass R]
    (A : Matrix I I R) (d : R) (hL : A.IsLowerTriangular) (hd : ∀ i, A i i = d) :
    A = Matrix.of (fun i j => if i ≤ j then 0 else A i j) +
      Matrix.diagonal (fun _ => d) := by
  ext i j
  change A i j = (if i ≤ j then 0 else A i j) + Matrix.diagonal (fun _ => d) i j
  rcases lt_trichotomy i j with hij | h | hji
  · simp [hL hij, le_of_lt hij, Matrix.diagonal_apply_ne _ (ne_of_lt hij)]
  · subst j
    simp [hd]
  · simp [not_le_of_gt hji, Matrix.diagonal_apply_ne _ (ne_of_gt hji)]

end Shape
#print axioms eq_of_actual_copies
#print axioms chronological_lower
end RKResearch.Certified.CausalStageMerge
