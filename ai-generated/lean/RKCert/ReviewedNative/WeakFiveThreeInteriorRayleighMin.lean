module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Logic.Equiv.Fin.Basic

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! # An algebraic bordered Rayleigh minimum

This lemma uses the elementary Schur identity over a trivially starred
ordered field, not a `StarOrderedRing` assumption. Positivity in the given
field need not coincide with sums of squares.
-/
namespace RKCert.ReviewedNative.ThreeInteriorPencil

open Matrix
open scoped Matrix BigOperators

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def rayleigh {ι : Type*} [Fintype ι] (M : Matrix ι ι K) (v : ι → K) : K :=
  v ⬝ᵥ (M *ᵥ v)

def leading {R : Type*} {n : ℕ} (M : Matrix (Fin (n+1)) (Fin (n+1)) R) :
    Matrix (Fin n) (Fin n) R := M.submatrix Fin.castSucc Fin.castSucc

def border {R : Type*} [Zero R] {n : ℕ} (d : R) : Matrix (Fin (n+1)) (Fin (n+1)) R :=
  Matrix.single (Fin.last n) (Fin.last n) d

def rayleighCost {n : ℕ} (M : Matrix (Fin (n+1)) (Fin (n+1)) K) : K :=
  M.det / (leading M).det

theorem rayleigh_relabel {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (M : Matrix κ κ K) (v : κ → K) :
    rayleigh (M.submatrix e e) (v ∘ e) = rayleigh M v := by
  unfold rayleigh
  rw [Matrix.submatrix_mulVec_equiv]
  have eq : (v ∘ e) ∘ e.symm = v := by funext i; simp
  rw [eq,comp_equiv_dotProduct_comp_equiv]

private theorem rayleigh_one (M : Matrix (Fin 1) (Fin 1) K) :
    rayleigh M (fun _ => 1) = M 0 0 := by
  simp [rayleigh, dotProduct, Matrix.mulVec]

section Min
variable [StarRing K] [TrivialStar K]

private theorem rayleigh_of_posDef_nonneg {ι : Type*} [Fintype ι] {M : Matrix ι ι K}
    (hM : M.PosDef) (v : ι → K) : 0 ≤ rayleigh M v := by
  by_cases z : v = 0
  · simp [rayleigh,z]
  · simpa only [rayleigh,star_trivial] using (hM.dotProduct_mulVec_pos z).le

/-- The infimum on the affine last-coordinate slice is attained, and
its value is the exact determinant ratio. -/
theorem rayleigh_min_of_posDef {n : ℕ} {M : Matrix (Fin (n+1)) (Fin (n+1)) K}
    (hM : M.PosDef) :
    0 < rayleighCost M ∧ ∃ v : Fin (n+1) → K, v (Fin.last n) = 1 ∧
      rayleigh M v = rayleighCost M ∧
      ∀ w : Fin (n+1) → K, w (Fin.last n) = 1 → rayleighCost M ≤ rayleigh M w := by
  let E : Fin n ⊕ Fin 1 ≃ Fin (n+1) := finSumFinEquiv
  have ein (i : Fin n) : E (.inl i) = i.castSucc := by apply Fin.ext; rfl
  have eout (i : Fin 1) : E (.inr i) = Fin.last n := by
    have z : i = 0 := Subsingleton.elim _ _
    subst i
    apply Fin.ext
    simp [E,Fin.val_natAdd]
  let A := leading M
  let B : Matrix (Fin n) (Fin 1) K := M.submatrix Fin.castSucc (fun _ => Fin.last n)
  let D : Matrix (Fin 1) (Fin 1) K := M.submatrix (fun _ => Fin.last n) (fun _ => Fin.last n)
  have hA : A.PosDef := hM.submatrix (Fin.castSucc_injective n)
  letI : Invertible A := hA.isUnit.invertible
  have blocks : M.submatrix E E = Matrix.fromBlocks A B Bᴴ D := by
    ext i j
    cases i with
    | inl i =>
      cases j with
      | inl j => simp only [Matrix.submatrix_apply,ein,Matrix.fromBlocks_apply₁₁,A,leading]
      | inr j => simp only [Matrix.submatrix_apply,ein,eout,Matrix.fromBlocks_apply₁₂,B]
    | inr i =>
      cases j with
      | inl j =>
        simp only [Matrix.submatrix_apply,ein,eout,Matrix.fromBlocks_apply₂₁,
          Matrix.conjTranspose_apply,B]
        exact (hM.isHermitian.apply (Fin.last n) j.castSucc).symm
      | inr j => simp only [Matrix.submatrix_apply,eout,Matrix.fromBlocks_apply₂₂,D]
  let F := D - Bᴴ*A⁻¹*B
  have det : M.det = A.det * F 0 0 := by
    calc
      M.det = (M.submatrix E E).det := (Matrix.det_submatrix_equiv_self E M).symm
      _ = A.det * F 0 0 := by
        rw [blocks,Matrix.det_fromBlocks₁₁,Matrix.invOf_eq_nonsing_inv,Matrix.det_fin_one]
  have rat : rayleighCost M = F 0 0 := by
    change M.det/A.det = F 0 0
    exact (congrArg (fun z : K => z / A.det) det).trans
      (mul_div_cancel_left₀ (F 0 0) hA.det_pos.ne')
  refine ⟨div_pos hM.det_pos hA.det_pos,?_⟩
  let y : Fin 1 → K := fun _ => 1
  let v₀ : Fin n → K := (A⁻¹*B) *ᵥ y
  have form (x : Fin n → K) :
      rayleigh (Matrix.fromBlocks A B Bᴴ D) (Sum.elim x y) =
        rayleigh A (x+v₀) + F 0 0 := by
    have e := Matrix.schur_complement_eq₁₁ B D x y hA.isHermitian
    simp only [star_trivial,← Matrix.dotProduct_mulVec] at e
    change rayleigh (Matrix.fromBlocks A B Bᴴ D) (Sum.elim x y) =
        rayleigh A (x+v₀) + rayleigh F y at e
    rw [show rayleigh F y = F 0 0 from rayleigh_one F] at e
    exact e
  let v : Fin (n+1) → K := Sum.elim (-v₀) y ∘ E.symm
  have ve : v ∘ E = Sum.elim (-v₀) y := by funext i; simp [v]
  refine ⟨v,?_,?_,?_⟩
  · rw [← eout (0 : Fin 1)]
    change (v ∘ E) (.inr 0) = 1
    rw [ve] <;> rfl
  · rw [← rayleigh_relabel E M v,ve,blocks,form,neg_add_cancel,rat]
    simp [rayleigh]
  · intro w wl
    let u : Fin n → K := fun i => w i.castSucc
    have wshape : w ∘ E = Sum.elim u y := by
      funext t
      cases t with
      | inl i => simp only [Function.comp_apply,ein,Sum.elim_inl,u]
      | inr i => simp only [Function.comp_apply,eout,Sum.elim_inr,y,wl]
    rw [← rayleigh_relabel E M w,wshape,blocks,form,rat]
    exact le_add_of_nonneg_left (rayleigh_of_posDef_nonneg hA (u+v₀))

end Min

section Border
variable {R : Type*} [CommRing R]

/-- The only diagonal update contributes exactly the leading minor,
even at a singular trial value. -/
theorem det_add_border {n : ℕ} (M : Matrix (Fin (n+1)) (Fin (n+1)) R) (d : R) :
    (M + border d).det = M.det + d*(leading M).det := by
  let k : Fin (n+1) := Fin.last n
  let W : Matrix (Fin (n+1)) (Fin (n+1)) R := M + border (n := n) d
  have minor (j : Fin (n+1)) :
      W.submatrix k.succAbove j.succAbove = M.submatrix k.succAbove j.succAbove := by
    ext a b
    simp only [W, Matrix.submatrix_apply, k, Fin.succAbove_last_apply, Matrix.add_apply, border,
      Matrix.single_apply_of_row_ne (Fin.castSucc_ne_last a).symm, add_zero]
  have row (j : Fin (n+1)) : W k j = M k j + (if j = k then d else 0) := by
    simp only [W, Matrix.add_apply, border]
    by_cases hj : j = k
    · subst j
      have entry : (Matrix.single (Fin.last n) (Fin.last n) d :
          Matrix (Fin (n+1)) (Fin (n+1)) R) k k = d := by
        simpa only [k] using (Matrix.single_apply_same (Fin.last n) (Fin.last n) d)
      simp only [entry, ite_true]
    · rw [Matrix.single_apply_of_col_ne k k (Ne.symm hj) d, ite_eq_right hj]
  let kept (j : Fin (n+1)) : R :=
    (-1 : R) ^ ((k : ℕ) + (j : ℕ)) * M k j * (M.submatrix k.succAbove j.succAbove).det
  let added (j : Fin (n+1)) : R :=
    (-1 : R) ^ ((k : ℕ) + (j : ℕ)) * (if j = k then d else 0) *
      (M.submatrix k.succAbove j.succAbove).det
  have split (j : Fin (n+1)) :
      (-1 : R) ^ ((k : ℕ) + (j : ℕ)) * W k j * (W.submatrix k.succAbove j.succAbove).det =
        kept j + added j := by
    rw [row j, minor j]
    dsimp only [kept, added]
    rw [mul_add, add_mul]
  have oldExpansion : M.det = ∑ j : Fin (n+1), kept j := Matrix.det_succ_row M k
  have oneSign : (-1 : R) ^ ((k : ℕ) + (k : ℕ)) = 1 := by
    change (-1 : R) ^ (n + n) = 1
    rw [← two_mul n, pow_mul, neg_one_sq, one_pow]
  have principal : (M.submatrix k.succAbove k.succAbove).det = (leading M).det := by
    simp only [k, Fin.succAbove_last, leading]
  have addedSum : (∑ j : Fin (n+1), added j) = d * (leading M).det := by
    rw [Finset.sum_eq_single_of_mem k (Finset.mem_univ k)]
    · simp only [added, ite_true, oneSign, one_mul, principal]
    · intro j _ hj
      simp only [added, ite_eq_right hj, mul_zero, zero_mul]
  change W.det = M.det + d * (leading M).det
  calc
    W.det = ∑ j : Fin (n+1),
        (-1 : R) ^ ((k : ℕ) + (j : ℕ)) * W k j * (W.submatrix k.succAbove j.succAbove).det :=
      Matrix.det_succ_row W k
    _ = ∑ j : Fin (n+1), (kept j + added j) := Finset.sum_congr rfl (fun j _ => split j)
    _ = M.det + ∑ j : Fin (n+1), added j := by
      rw [Finset.sum_add_distrib, ← oldExpansion]
    _ = M.det + d * (leading M).det := congrArg (fun x : R => M.det + x) addedSum

end Border
end
end RKCert.ReviewedNative.ThreeInteriorPencil
