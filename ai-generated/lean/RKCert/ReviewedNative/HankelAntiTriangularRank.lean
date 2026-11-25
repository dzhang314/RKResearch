module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import RKCert.ReviewedNative.HankelFirstAntidiagonalDet
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Logic.Equiv.Fin.Basic

import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # The rank of a delayed nonzero antidiagonal

All rank steps use Mathlib Matrix.rank. The single block connector is
the standard product of existing mulVec linear maps. -/
namespace RKResearch.Certified.Graded.HankelAntiTriangularRank

open Matrix Module
open scoped Matrix

noncomputable section

variable {K : Type*} [Field K]

/-- The only block rank calculation needed: use the existing range
and product equivalences, not a second rank definition. -/
theorem rank_fromBlocks_zero_cross {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι ι K) (B : Matrix κ κ K) :
    (Matrix.fromBlocks A 0 0 B).rank = A.rank + B.rank := by
  let e := LinearEquiv.sumArrowLequivProdArrow ι κ K K
  let F := A.mulVecLin.prodMap B.mulVecLin
  let M := (Matrix.fromBlocks A 0 0 B).mulVecLin
  have h : e.toLinearMap.comp M = F.comp e.toLinearMap := by
    apply LinearMap.ext
    intro v
    change e ((Matrix.fromBlocks A 0 0 B) *ᵥ v) = F (e v)
    rw [Matrix.fromBlocks_mulVec]
    apply Prod.ext
    · funext i
      simp [e,F,Matrix.zero_mulVec,Function.comp_def] <;>
        exact congrArg (fun w : ι → K => (A *ᵥ w) i)
          (funext (fun j => (LinearEquiv.sumArrowLequivProdArrow_apply_fst (R := K) (M := K) v j).symm))
    · funext i
      simp [e,F,Matrix.zero_mulVec,Function.comp_def] <;>
        exact congrArg (fun w : κ → K => (B *ᵥ w) i)
          (funext (fun j => (LinearEquiv.sumArrowLequivProdArrow_apply_snd (R := K) (M := K) v j).symm))
  have ran : M.range.map e.toLinearMap = A.mulVecLin.range.prod B.mulVecLin.range := by
    rw [← LinearMap.range_comp, h, LinearMap.range_comp,
      LinearEquiv.range, Submodule.map_top]
    change (A.mulVecLin.prodMap B.mulVecLin).range = _
    exact LinearMap.range_prodMap _ _
  change finrank K M.range = finrank K A.mulVecLin.range + finrank K B.mulVecLin.range
  rw [← e.finrank_map_eq M.range, ran,
    (Submodule.prodEquiv A.mulVecLin.range B.mulVecLin.range).finrank_eq, Module.finrank_prod]

/-- Full rank is a direct consumer of the backed determinant seed. -/
theorem rank_first_antidiagonal {n : ℕ} (M : Matrix (Fin n) (Fin n) K)
    (zero : ∀ i j : Fin n, i.val+j.val < n-1 → M i j=0)
    (live : ∀ i j : Fin n, i.val+j.val = n-1 → M i j≠0) :
    M.rank=n := by
  simpa only [Fintype.card_fin] using
    Matrix.rank_of_det_ne_zero (det_ne_zero_of_first_antidiagonal M zero live)

/-- If the nonzero antidiagonal has not been paid at this width, its
nonzeroness is not a hypothesis. Otherwise exactly the terminal
(2q−s−1)-square contributes to the rank. -/
theorem rank_delayed_antidiagonal {q s : ℕ} (qs : q≤s+1)
    (M : Matrix (Fin q) (Fin q) K)
    (zero : ∀ i j : Fin q, i.val+j.val < s → M i j=0)
    (live : ∀ i j : Fin q, i.val+j.val = s → M i j≠0) :
    M.rank = 2*q-(s+1) := by
  by_cases dead : 2*q≤s+1
  · have eq : M=0 := by
      ext i j
      apply zero
      have hi := i.isLt
      have hj := j.isLt
      omega
    rw [eq,Matrix.rank_zero]
    omega
  let e := s+1-q
  let m := q-e
  have e_add_q : e+q=s+1 := by dsimp only [e]; omega
  have emq : e+m=q := by dsimp only [m,e]; omega
  have mq : m=2*q-(s+1) := by omega
  have mp : 0<m := by omega
  have es : 2*e+(m-1)=s := by omega
  let idx : Fin e ⊕ Fin m ≃ Fin q := finSumFinEquiv.trans (finCongr emq)
  have li (i : Fin e) : (idx (Sum.inl i)).val=i.val := by simp [idx]
  have ri (i : Fin m) : (idx (Sum.inr i)).val=e+i.val := by simp [idx]
  let C := M.submatrix (fun i => idx (Sum.inr i)) (fun i => idx (Sum.inr i))
  have left (i : Fin e) (j : Fin q) : M (idx (Sum.inl i)) j=0 := by
    apply zero
    rw [li]
    have a := i.isLt
    have b := j.isLt
    omega
  have right (i : Fin q) (j : Fin e) : M i (idx (Sum.inl j))=0 := by
    apply zero
    rw [li]
    have a := i.isLt
    have b := j.isLt
    omega
  have shape : M.submatrix idx idx =
      Matrix.fromBlocks (0 : Matrix (Fin e) (Fin e) K) 0 0 C := by
    ext i j
    cases i with
    | inl i =>
      cases j with
      | inl j => exact left i _
      | inr j => exact left i _
    | inr i =>
      cases j with
      | inl j => exact right _ j
      | inr j => rfl
  have cr : C.rank=m := by
    apply rank_first_antidiagonal
    · intro i j ij
      change M (idx (Sum.inr i)) (idx (Sum.inr j))=0
      apply zero
      simp only [ri]
      omega
    · intro i j ij
      change M (idx (Sum.inr i)) (idx (Sum.inr j))≠0
      apply live
      simp only [ri]
      omega
  calc
    M.rank = (M.submatrix idx idx).rank := (Matrix.rank_submatrix M idx idx).symm
    _ = C.rank := by rw [shape,rank_fromBlocks_zero_cross,Matrix.rank_zero,zero_add]
    _ = 2*q-(s+1) := cr.trans mq

end
end RKResearch.Certified.Graded.HankelAntiTriangularRank
