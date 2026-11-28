module

public import RKCert.ReviewedNative.GradedColumns
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Tactic.Ring

@[expose] public section

/-! Actual adjacent-row commutator debit and four-clock pure cancellation. -/
namespace RKResearch.Certified.Graded.OrderTwelveFifteen.UniformGapCore

open scoped Matrix BigOperators

variable {K : Type*} [Field K] {n : ℕ}
  {A : Matrix (Fin n) (Fin n) K}

/-- A genuine degree-three multiplier of a weighted pure head cannot
have four distinct zeros where the leading head is nonzero. -/
theorem fourLiveClockZeros (p : Polynomial K) (deg : p.natDegree ≤ 3)
    (c h : Fin 4 → K) (distinct : Function.Injective c)
    (live : ∀ i, h i ≠ 0) (z : ∀ i, h i * p.eval (c i) = 0) : p=0 := by
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero p distinct
  · intro i
    exact (mul_eq_zero.mp (z i)).resolve_left (live i)
  · simpa using (Nat.lt_succ_of_le deg : p.natDegree < 4)

private theorem readZeroEarlier (ha : A.IsLowerTriangular)
    {i : Fin n} {v : Fin n → K} (hh : ∀ k, k < i → v k = 0) :
    ∀ k, k < i → (A *ᵥ v) k = 0 := by
  classical
  intro k hk
  rw [Matrix.mulVec,dotProduct]
  apply Finset.sum_eq_zero
  intro l _
  by_cases h : l ≤ k
  · rw [hh l (lt_of_le_of_lt h hk),mul_zero]
  · rw [ha (lt_of_not_ge h),zero_mul]

private theorem readAt (ha : A.IsLowerTriangular)
    {i : Fin n} {v : Fin n → K} (hh : ∀ k, k < i → v k = 0) :
    (A *ᵥ v) i = A i i * v i := by
  classical
  rw [Matrix.mulVec,dotProduct]
  refine Finset.sum_eq_single i ?_ (by simp)
  intro k _ hi
  rcases lt_or_gt_of_ne hi with h | h
  · rw [hh k h,mul_zero]
  · rw [ha h,zero_mul]

private theorem readAdjacent (ha : A.IsLowerTriangular)
    {i j : Fin n} (adj : j.val=i.val+1) {v : Fin n → K}
    (hh : ∀ k, k < i → v k = 0) :
    (A *ᵥ v) j = A j i * v i + A j j * v j := by
  classical
  rw [Matrix.mulVec,dotProduct]
  have nij : i ≠ j := by
    intro h
    rw [h] at adj
    omega
  calc
    _ = ∑ k ∈ ({i,j}:Finset (Fin n)), A j k * v k := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro k _ hk
      simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hk
      by_cases h : k < i
      · rw [hh k h,mul_zero]
      · have hval : j.val < k.val := by
          have n1 : k.val ≠ i.val := fun e => hk.1 (Fin.eq_of_val_eq e)
          have n2 : k.val ≠ j.val := fun e => hk.2 (Fin.eq_of_val_eq e)
          have h' : i.val ≤ k.val := le_of_not_gt h
          omega
        rw [ha (show j < k from hval),zero_mul]
    _ = _ := by simp [Finset.sum_insert,nij]

/-- The coordinate of CA−AC−A², with the diagonal clock applied literally. -/
def commRead (A : Matrix (Fin n) (Fin n) K) (c v : Fin n → K) (j : Fin n) : K :=
  c j * (A *ᵥ v) j - (A *ᵥ fun k => c k * v k) j - (A *ᵥ (A *ᵥ v)) j

/-- The explicit first pivot has zero first primitive, so the next
physical row depends only on the two displayed chronological inputs. -/
theorem adjacentCommRead (ha : A.IsLowerTriangular) (c : Fin n → K)
    {i j : Fin n} (adj : j.val=i.val+1) (explicit : A i i=0)
    {v : Fin n → K} (hh : ∀ k, k < i → v k = 0) :
    commRead A c v j =
      (c j-c i-A j j)*(A j i * v i)-(A j j)^2*v j := by
  have hcv : ∀ k, k < i → (fun l => c l * v l) k=0 := by
    intro k h
    simp [hh k h]
  have hv0 : (A *ᵥ v) i=0 := by rw [readAt ha hh,explicit,zero_mul]
  rw [commRead,readAdjacent ha adj hh,readAdjacent ha adj hcv,
    readAdjacent ha adj (readZeroEarlier ha hh),hv0,mul_zero,zero_add,
    readAdjacent ha adj hh]
  ring

/-- On a truly adjacent pair after an explicit pivot, the two zero
commutators force the same numerical clock and the second zero diagonal. -/
theorem adjacentSameClock (ha : A.IsLowerTriangular) (c : Fin n → K)
    {i j : Fin n} (adj : j.val=i.val+1) (explicit : A i i=0)
    {z w : Fin n → K} (hz : ∀ k, k < i → z k=0) (hw : ∀ k, k < i → w k=0)
    (zj : z j=0) (wjnz : w j≠0) (live : (A *ᵥ z) j≠0)
    (c1 : commRead A c z j=0) (c2 : commRead A c w j=0) :
    A j j=0 ∧ c j=c i := by
  have tap : A j i * z i≠0 := by
    simpa [readAdjacent ha adj hz,zj] using live
  have h1 : (c j-c i-A j j)*(A j i*z i)=0 := by
    simpa [adjacentCommRead ha c adj explicit hz,zj] using c1
  have eq : c j-c i-A j j=0 := (mul_eq_zero.mp h1).resolve_right tap
  have h2 : (A j j)^2*w j=0 := by
    simpa [adjacentCommRead ha c adj explicit hw,eq] using c2
  have d : A j j=0 := by
    by_contra nz
    exact (mul_ne_zero (pow_ne_zero 2 nz) wjnz) h2
  exact ⟨d,sub_eq_zero.mp (by simpa [d] using eq)⟩

#print axioms fourLiveClockZeros
#print axioms adjacentCommRead
#print axioms adjacentSameClock

end RKResearch.Certified.Graded.OrderTwelveFifteen.UniformGapCore
