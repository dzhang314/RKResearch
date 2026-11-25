module

public import RKCert.ReviewedNative.MergeEqualRows
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.LinearAlgebra.Matrix.Block

@[expose] public section

namespace RKResearch.Certified.DiagonalTwin

open RKResearch FiniteRootedTree
open RKResearch.Certified.Graded (mergeCoefficient sum_merge_coefficient)
open scoped Matrix

variable {n p : ℕ}

/-- Retained stages in their original order. -/
def compressStages {R : Type*} (j : Fin (n + 1))
    (v : Fin (n + 1) → R) : Fin n → R :=
  fun k => v (j.succAbove k)

/-- Fill the deleted stage with the retained representative's value. -/
def lift {R : Type*} (j : Fin (n + 1)) (r : Fin n)
    (v : Fin n → R) : Fin (n + 1) → R :=
  Fin.insertNth (α := fun _ => R) j (v r) v

@[simp] theorem lift_deleted {R : Type*} (j : Fin (n + 1))
    (r : Fin n) (v : Fin n → R) : lift j r v j = v r := by
  simp only [lift, Fin.insertNth_apply_same]

@[simp] theorem lift_retained {R : Type*} (j : Fin (n + 1))
    (r : Fin n) (v : Fin n → R) (k : Fin n) :
    lift j r v (j.succAbove k) = v k := by
  simp only [lift, Fin.insertNth_apply_succAbove]

@[simp] theorem compressStages_lift {R : Type*} (j : Fin (n + 1))
    (r : Fin n) (v : Fin n → R) : compressStages j (lift j r v) = v := by
  funext k
  exact lift_retained j r v k

section Semiring

variable {R : Type*} [CommSemiring R]

/-- `P A U`: retain rows and sum the two identified columns. -/
def contractMatrix (j : Fin (n + 1)) (r : Fin n)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    Matrix (Fin n) (Fin n) R :=
  fun k => mergeCoefficient j r (A (j.succAbove k))

/-- Equality of the two rows on all lifted columns. -/
def RowsBalanced (j : Fin (n + 1)) (r : Fin n)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) : Prop :=
  ∀ k, mergeCoefficient j r (A j) k =
    mergeCoefficient j r (A (j.succAbove r)) k

private theorem lift_one (j : Fin (n + 1)) (r : Fin n) :
    lift j r (1 : Fin n → R) = 1 := by
  apply funext
  rw [Fin.forall_iff_succAbove j]
  constructor
  · simp only [lift_deleted, Pi.one_apply]
  · intro k
    simp only [lift_retained, Pi.one_apply]

private theorem lift_mul (j : Fin (n + 1)) (r : Fin n) (u v : Fin n → R) :
    lift j r (u * v) = lift j r u * lift j r v := by
  apply funext
  rw [Fin.forall_iff_succAbove j]
  constructor
  · simp only [lift_deleted, Pi.mul_apply]
  · intro k
    simp only [lift_retained, Pi.mul_apply]

/-- Transposing the lift adds the deleted entry to the output covector. -/
theorem dotProduct_lift (j : Fin (n + 1)) (r : Fin n)
    (w : Fin (n + 1) → R) (v : Fin n → R) :
    w ⬝ᵥ lift j r v = mergeCoefficient j r w ⬝ᵥ v := by
  have eq : lift j r v j = lift j r v (j.succAbove r) := by
    simp only [lift_deleted, lift_retained]
  symm
  simpa only [dotProduct, lift_retained] using
    sum_merge_coefficient j r w (lift j r v) eq

theorem mulVec_lift (j : Fin (n + 1)) (r : Fin n)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (h : RowsBalanced j r A) (v : Fin n → R) :
    A *ᵥ lift j r v = lift j r (contractMatrix j r A *ᵥ v) := by
  apply funext
  rw [Fin.forall_iff_succAbove j]
  constructor
  · rw [lift_deleted]
    change A j ⬝ᵥ lift j r v =
      mergeCoefficient j r (A (j.succAbove r)) ⬝ᵥ v
    rw [dotProduct_lift]
    exact congrArg (fun w : Fin n → R => w ⬝ᵥ v) (funext (fun k => h k))
  · intro k
    rw [lift_retained]
    change A (j.succAbove k) ⬝ᵥ lift j r v =
      mergeCoefficient j r (A (j.succAbove k)) ⬝ᵥ v
    exact dotProduct_lift j r _ v

theorem phi_contract (j : Fin (n + 1)) (r : Fin n)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (h : RowsBalanced j r A) (t : FiniteRootedTree) :
    Φ t A = lift j r (Φ t (contractMatrix j r A)) := by
  induction t with
  | leaf => simp only [Φ, lift_one]
  | butcherProduct u v hu hv =>
    simp only [Φ]
    rw [hu, hv, mulVec_lift j r A h, lift_mul]

theorem dotProduct_phi_contract (j : Fin (n + 1)) (r : Fin n)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (h : RowsBalanced j r A) (b : Fin (n + 1) → R) (t : FiniteRootedTree) :
    mergeCoefficient j r b ⬝ᵥ Φ t (contractMatrix j r A) = b ⬝ᵥ Φ t A := by
  rw [phi_contract j r A h t, dotProduct_lift]

theorem hasOrder_contract_iff (j : Fin (n + 1)) (r : Fin n)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (h : RowsBalanced j r A) (b : Fin (n + 1) → R) :
    HasOrder p (contractMatrix j r A) (mergeCoefficient j r b) ↔
      HasOrder p A b := by
  unfold HasOrder
  simp only [dotProduct_phi_contract j r A h b]

theorem rowsBalanced_of_common_row (j : Fin (n + 1)) (r : Fin n)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (γ : R) (q : Fin (n + 1) → R)
    (hd : ∀ k, A j k = q k + (if k = j then γ else 0))
    (hr : ∀ k, A (j.succAbove r) k =
      q k + (if k = j.succAbove r then γ else 0)) :
    RowsBalanced j r A := by
  intro k
  by_cases hk : k = r
  · subst k
    simp only [mergeCoefficient, if_pos rfl, hd, hr,
      if_neg (Fin.succAbove_ne j r), if_neg (Fin.ne_succAbove j r), add_zero]
    exact (add_assoc _ _ _).symm.trans (add_right_comm _ _ _)
  · have hkr : j.succAbove k ≠ j.succAbove r :=
      fun h => hk (Fin.succAbove_right_inj.mp h)
    simp only [mergeCoefficient, if_neg hk, hd, hr,
      if_neg (Fin.succAbove_ne j k), if_neg hkr, add_zero]

theorem contract_lower (j : Fin (n + 1)) (r : Fin n)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (hchron : j.succAbove r < j) (ha : A.IsLowerTriangular) :
    (contractMatrix j r A).IsLowerTriangular := by
  have hz (a k : Fin (n + 1)) (h : a < k) : A a k = 0 := ha h
  intro a k hak
  change a < k at hak
  have h : j.succAbove a < j.succAbove k := Fin.strictMono_succAbove j hak
  by_cases hk : k = r
  · subst k
    simp [contractMatrix, mergeCoefficient, hz _ _ h, hz _ _ (h.trans hchron)]
  · simp only [contractMatrix, mergeCoefficient, if_neg hk, hz _ _ h, add_zero]

theorem contract_diagonal (j : Fin (n + 1)) (r : Fin n)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (hchron : j.succAbove r < j) (ha : A.IsLowerTriangular) (k : Fin n) :
    contractMatrix j r A k k = A (j.succAbove k) (j.succAbove k) := by
  have hz : A (j.succAbove r) j = 0 := ha hchron
  by_cases hk : k = r
  · subst k
    simp only [contractMatrix, mergeCoefficient, ite_true, hz, add_zero]
  · simp only [contractMatrix, mergeCoefficient, if_neg hk, add_zero]

end Semiring

section Ring

variable {R : Type*} [CommRing R]

def DiagonalTwins (j : Fin (n + 1)) (r : Fin n) (γ : R)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) : Prop :=
  ∀ k, A j k - (if k = j then γ else 0) =
    A (j.succAbove r) k - (if k = j.succAbove r then γ else 0)

theorem rowsBalanced_of_diagonalTwins
    {j : Fin (n + 1)} {r : Fin n} {γ : R}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) R} (h : DiagonalTwins j r γ A) :
    RowsBalanced j r A := by
  refine rowsBalanced_of_common_row j r A γ
    (fun k => A (j.succAbove r) k - (if k = j.succAbove r then γ else 0)) ?_ ?_
  · intro k
    change A j k = (A (j.succAbove r) k -
      (if k = j.succAbove r then γ else 0)) + (if k = j then γ else 0)
    rw [← h k, sub_add_cancel]
  · intro k
    exact (sub_add_cancel _ _).symm

theorem phi_diagonalTwins {j : Fin (n + 1)} {r : Fin n} {γ : R}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) R}
    (h : DiagonalTwins j r γ A) (t : FiniteRootedTree) :
    Φ t A = lift j r (Φ t (contractMatrix j r A)) :=
  phi_contract j r A (rowsBalanced_of_diagonalTwins h) t

theorem hasOrder_diagonalTwins_iff {j : Fin (n + 1)} {r : Fin n} {γ : R}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) R}
    (h : DiagonalTwins j r γ A) (b : Fin (n + 1) → R) :
    HasOrder p (contractMatrix j r A) (mergeCoefficient j r b) ↔
      HasOrder p A b :=
  hasOrder_contract_iff j r A (rowsBalanced_of_diagonalTwins h) b

theorem contract_strict_sdirk {j : Fin (n + 1)} {r : Fin n} {γ : R}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) R} {b : Fin (n + 1) → R}
    (hchron : j.succAbove r < j) (ha : A.IsLowerTriangular)
    (hc : ∀ k, A k k = γ) (hγ : γ ≠ 0)
    (ht : DiagonalTwins j r γ A) (ho : HasOrder p A b) :
    (contractMatrix j r A).IsLowerTriangular ∧
    (∀ k, contractMatrix j r A k k = γ) ∧ γ ≠ 0 ∧
    HasOrder p (contractMatrix j r A) (mergeCoefficient j r b) :=
  ⟨contract_lower j r A hchron ha,
    fun k => (contract_diagonal j r A hchron ha k).trans (hc _),
    hγ, (hasOrder_diagonalTwins_iff ht b).mpr ho⟩

end Ring

end RKResearch.Certified.DiagonalTwin
