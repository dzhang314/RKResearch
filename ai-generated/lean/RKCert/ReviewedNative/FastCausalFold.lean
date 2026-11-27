module

public import RKCert.ReviewedNative.CausalStageMerge
public import RKCert.ReviewedNative.TailMatrixReceipts

@[expose] public section

/-! The actual copied-head quotient can evaluate using only the few copied
coordinates, rather than enumerating an entire fiber for each access. -/

namespace RKResearch.Certified.CausalStageMerge

open TwoDonorDense TwoOrderMomentTail
open scoped Matrix BigOperators

def copyIndex (old fresh : ℕ) {copies : ℕ} (i : Fin copies) : Fin (old+copies+fresh) :=
  ⟨old+i.val, by have := i.isLt; omega⟩

def classifyIndex (old copies fresh : ℕ) (i : Fin (old+copies+fresh)) :
    Fin (old+fresh) ⊕ Fin copies :=
  if h : i.val < old then .inl ⟨i.val, by omega⟩
  else if h' : i.val < old+copies then .inr ⟨i.val-old, by omega⟩
  else .inl ⟨i.val-copies, by have := i.isLt; omega⟩

theorem classify_keep (old copies fresh : ℕ) (i : Fin (old+fresh)) :
    classifyIndex old copies fresh (keepHead old copies fresh i) = Sum.inl i := by
  by_cases h : i.val < old
  · simp [classifyIndex, keepHead, h]
  · have h' : ¬ i.val+copies < old := by omega
    have h'' : ¬ i.val+copies < old+copies := by omega
    simp [classifyIndex, keepHead, h, h', h'']

theorem classify_copy (old fresh : ℕ) {copies : ℕ} (i : Fin copies) :
    classifyIndex old copies fresh (copyIndex old fresh i) = Sum.inr i := by
  have hi := i.isLt
  have h : ¬ old+i.val < old := by omega
  have h' : old+i.val < old+copies := by omega
  simp [classifyIndex, copyIndex, h, h']

theorem classify_full (old copies fresh : ℕ) (i : Fin (old+copies+fresh)) :
    Sum.elim (keepHead old copies fresh) (copyIndex old fresh)
      (classifyIndex old copies fresh i) = i := by
  apply Fin.ext
  by_cases h : i.val < old
  · simp [classifyIndex, keepHead, h]
  · by_cases h' : i.val < old+copies
    · simp [classifyIndex, keepHead, copyIndex, h, h']
      omega
    · have h'' : ¬ i.val-copies < old := by omega
      simp [classifyIndex, keepHead, h, h', h'']
      omega

/-- Explicit order-free decomposition of the large stage index into retained
coordinates and the intervening copied block. -/
def splitCopyEquiv (old copies fresh : ℕ) :
    Fin (old+fresh) ⊕ Fin copies ≃ Fin (old+copies+fresh) where
  toFun := Sum.elim (keepHead old copies fresh) (copyIndex old fresh)
  invFun := classifyIndex old copies fresh
  left_inv := by
    intro i
    cases i with
    | inl i => exact classify_keep old copies fresh i
    | inr i => exact classify_copy old fresh i
  right_inv := classify_full old copies fresh

def donorLift (fresh : ℕ) {old : ℕ} (i : Fin old) : Fin (old+fresh) := i.castAdd fresh

theorem redirect_copy {old fresh copies : ℕ} (donors : Fin copies → Fin old) (i : Fin copies) :
    redirectHead (fresh := fresh) donors (copyIndex old fresh i) = donorLift fresh (donors i) := by
  have hi := i.isLt
  have h : ¬ old+i.val < old := by omega
  have h' : old+i.val < old+copies := by omega
  apply Fin.ext
  simp [redirectHead, copyIndex, donorLift, h, h']

theorem sum_folded_head {old copies fresh : ℕ} {R : Type*} [AddCommMonoid R]
    (donors : Fin copies → Fin old) (f : Fin (old+copies+fresh) → R) (k : Fin (old+fresh)) :
    (∑ j ∈ fiber (redirectHead donors) k, f j) =
      f (keepHead old copies fresh k) +
      ∑ i : Fin copies, if donorLift fresh (donors i) = k then f (copyIndex old fresh i) else 0 := by
  unfold fiber
  rw [Finset.sum_filter]
  have h := Fintype.sum_equiv (splitCopyEquiv old copies fresh)
    (fun x => if redirectHead donors (splitCopyEquiv old copies fresh x) = k then
      f (splitCopyEquiv old copies fresh x) else 0)
    (fun j => if redirectHead donors j = k then f j else 0) (fun _ => rfl)
  rw [← h]
  simp [Fintype.sum_sum_type, splitCopyEquiv, redirect_keepHead, redirect_copy]

def fastFoldMatrix {old copies fresh : ℕ} {K : Type*} [CommSemiring K]
    (donors : Fin copies → Fin old) (A : Matrix (Fin (old+copies+fresh)) (Fin (old+copies+fresh)) K) :
    Matrix (Fin (old+fresh)) (Fin (old+fresh)) K := fun i j =>
  A (keepHead old copies fresh i) (keepHead old copies fresh j) +
    ∑ c : Fin copies, if donorLift fresh (donors c) = j
      then A (keepHead old copies fresh i) (copyIndex old fresh c) else 0

def fastFoldWeights {old copies fresh : ℕ} {K : Type*} [CommSemiring K]
    (donors : Fin copies → Fin old) (b : Fin (old+copies+fresh) → K) : Fin (old+fresh) → K := fun j =>
  b (keepHead old copies fresh j) +
    ∑ c : Fin copies, if donorLift fresh (donors c) = j then b (copyIndex old fresh c) else 0

theorem fastFoldMatrix_eq {old copies fresh : ℕ} {K : Type*} [CommSemiring K]
    (donors : Fin copies → Fin old) (A : Matrix (Fin (old+copies+fresh)) (Fin (old+copies+fresh)) K) :
    fastFoldMatrix (fresh := fresh) donors A =
      foldedMatrix (redirectHead donors) (keepHead old copies fresh) A := by
  ext i j
  symm
  exact sum_folded_head donors (A (keepHead old copies fresh i)) j

theorem fastFoldWeights_eq {old copies fresh : ℕ} {K : Type*} [CommSemiring K]
    (donors : Fin copies → Fin old) (b : Fin (old+copies+fresh) → K) :
    fastFoldWeights (fresh := fresh) donors b = foldedWeights (redirectHead donors) b := by
  funext j
  exact (sum_folded_head donors b j).symm

theorem pure_folded_iff {I J K : Type*} [Fintype I] [Fintype J] [DecidableEq J] [CommSemiring K]
    {A : Matrix I I K} {π : I → J} {keep : J → I} (h : Respects A π keep) (i : I) (r : ℕ) :
    PureAt A i r ↔ PureAt (foldedMatrix π keep A) (π i) r := by
  have hc : clocks A = clocks (foldedMatrix π keep A) ∘ π := mulVec_pullback h 1
  unfold PureAt normalized
  simp only [phi_pullback h, hc, Function.comp_apply, Pi.smul_apply]

theorem pure_shifted_iff {I J K : Type*} [Fintype I] [Fintype J] [CommSemiring K]
    (A : Matrix I I K) (e : I ≃ J) (i : J) (r : ℕ) :
    PureAt (shifted e A) i r ↔ PureAt A (e.symm i) r := by
  have hc : clocks (shifted e A) = clocks A ∘ e.symm := action_shifted e A 1
  unfold PureAt normalized
  simp only [phi_shifted, hc, Function.comp_apply, Pi.smul_apply]

#print axioms fastFoldMatrix_eq
#print axioms pure_folded_iff
end RKResearch.Certified.CausalStageMerge
