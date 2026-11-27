module

public import RKResearch.OrderConditions
public import Mathlib.LinearAlgebra.Matrix.Block

@[expose] public section

/-!
# Causal literal-stage merges for ordinary Runge–Kutta order

A pullback of stage vectors along a finite quotient intertwines both
the matrix action and componentwise multiplication. Literal copies of a
strict predecessor row have this property even though their self taps
are at different coordinates. Causality then preserves the common
diagonal when duplicate columns are redirected to earlier originals.
-/

namespace RKResearch.Certified.CausalStageMerge

open FiniteRootedTree
open scoped Matrix FiniteRootedTree BigOperators

variable {I J R : Type*} [Fintype I] [Fintype J] [DecidableEq J] [CommSemiring R]

def fiber (π : I → J) (k : J) : Finset I := Finset.univ.filter fun i => π i = k

def foldedWeights (π : I → J) (b : I → R) : J → R :=
  fun k => ∑ j ∈ fiber π k, b j

def foldedMatrix (π : I → J) (keep : J → I) (A : Matrix I I R) : Matrix J J R :=
  fun i k => ∑ j ∈ fiber π k, A (keep i) j

/-- Finite pushforward on coefficient rows is adjoint to pullback on stage values. -/
theorem dot_foldedWeights (π : I → J) (b : I → R) (v : J → R) :
    foldedWeights π b ⬝ᵥ v = b ⬝ᵥ (v ∘ π) := by
  simp only [foldedWeights, dotProduct, Finset.sum_mul, Function.comp_apply]
  calc
    _ = ∑ k : J, ∑ j ∈ fiber π k, b j * v (π j) := by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro j hj
      rw [(Finset.mem_filter.mp hj).2]
    _ = _ := Finset.sum_fiberwise Finset.univ π _

/-- A sufficient stage equation condition for an exact quotient on all rooted trees. -/
def Respects (A : Matrix I I R) (π : I → J) (keep : J → I) : Prop :=
  ∀ i k, (∑ j ∈ fiber π k, A i j) = foldedMatrix π keep A (π i) k

theorem mulVec_pullback {A : Matrix I I R} {π : I → J} {keep : J → I}
    (hr : Respects A π keep) (v : J → R) :
    A *ᵥ (v ∘ π) = ((foldedMatrix π keep A) *ᵥ v) ∘ π := by
  funext i
  change A i ⬝ᵥ (v ∘ π) = foldedMatrix π keep A (π i) ⬝ᵥ v
  rw [← dot_foldedWeights]
  congr 1
  funext k; exact hr i k

theorem phi_pullback {A : Matrix I I R} {π : I → J} {keep : J → I}
    (hr : Respects A π keep) (t : FiniteRootedTree) :
    Φ t A = Φ t (foldedMatrix π keep A) ∘ π := by
  induction t with
  | leaf => rfl
  | butcherProduct t u ht hu =>
    simp only [Φ, ht, hu, mulVec_pullback hr]
    rfl

theorem hasOrder_iff_folded {A : Matrix I I R} {π : I → J} {keep : J → I}
    (hr : Respects A π keep) (b : I → R) (p : ℕ) :
    HasOrder p A b ↔ HasOrder p (foldedMatrix π keep A) (foldedWeights π b) := by
  simp only [HasOrder, phi_pullback hr, dot_foldedWeights]

omit [Fintype J] in
theorem diag_fiber [DecidableEq I] (π : I → J) (γ : R) (i : I) (k : J) :
    (∑ j ∈ fiber π k, Matrix.diagonal (fun _ : I => γ) i j) =
      if π i = k then γ else 0 := by
  simp [Matrix.diagonal_apply, fiber]

omit [Fintype J] in
/-- Literal copies share their entire strict row (with the common
self coefficient removed). In the quotient the self terms agree as well. -/
theorem respects_literal [DecidableEq I] (D : Matrix I I R) (γ : R)
    (π : I → J) (keep : J → I) (hkeep : ∀ i, π (keep i) = i)
    (hrows : ∀ i j, D i j = D (keep (π i)) j) :
    Respects (D + Matrix.diagonal (fun _ : I => γ)) π keep := by
  intro i k
  simp only [foldedMatrix, Matrix.add_apply, Finset.sum_add_distrib, diag_fiber, hkeep]
  congr 1
  apply Finset.sum_congr rfl
  exact fun j _ => hrows i j

section Ordered
variable [LinearOrder I] [LinearOrder J]

omit [Fintype J] in
/-- Redirecting only to earlier originals keeps the matrix lower triangular. -/
theorem lower_folded {A : Matrix I I R} (hA : A.IsLowerTriangular)
    {π : I → J} {keep : J → I} (hmono : StrictMono keep) (hearly : ∀ i, keep (π i) ≤ i) :
    (foldedMatrix π keep A).IsLowerTriangular := by
  change ∀ ⦃i k : J⦄, i < k → foldedMatrix π keep A i k = 0
  intro i k h
  apply Finset.sum_eq_zero
  intro j hj
  have hj' := (Finset.mem_filter.mp hj).2
  have hlt : keep i < j := lt_of_lt_of_le (hmono h) (hj' ▸ hearly j)
  exact hA hlt

omit [Fintype J] [LinearOrder J] in
/-- On a diagonal fiber, every deleted copy has a later original column
index than the retained row. Such contributions vanish by triangularity. -/
theorem diag_folded {A : Matrix I I R} (hA : A.IsLowerTriangular)
    {π : I → J} {keep : J → I} (hkeep : ∀ i, π (keep i) = i)
    (hearly : ∀ i, keep (π i) ≤ i) (i : J) :
    foldedMatrix π keep A i i = A (keep i) (keep i) := by
  change (∑ j ∈ fiber π i, A (keep i) j) = _
  apply Finset.sum_eq_single (keep i)
  · intro j hj hne
    have hj' := (Finset.mem_filter.mp hj).2
    have hle : keep i ≤ j := hj' ▸ hearly j
    have hlt : keep i < j := lt_of_le_of_ne hle hne.symm
    exact hA hlt
  · simp [fiber, hkeep]

/-- A theorem giving the strict lower structure, unchanged common diagonal,
and equivalent order predicates for any causal literal quotient. -/
theorem strictSDIRK_merge [DecidableEq I] (D : Matrix I I R) (γ : R)
    (π : I → J) (keep : J → I) (hkeep : ∀ i, π (keep i) = i)
    (hmono : StrictMono keep) (hearly : ∀ i, keep (π i) ≤ i)
    (hrows : ∀ i j, D i j = D (keep (π i)) j)
    (hstrict : ∀ i j, i ≤ j → D i j = 0) (b : I → R) (p : ℕ) :
    let A := D + Matrix.diagonal (fun _ : I => γ)
    let A' := foldedMatrix π keep A
    A'.IsLowerTriangular ∧ (∀ i, A' i i = γ) ∧
      (HasOrder p A b ↔ HasOrder p A' (foldedWeights π b)) := by
  dsimp only
  let A := D + Matrix.diagonal (fun _ : I => γ)
  have hA : A.IsLowerTriangular := by
    change ∀ ⦃i j : I⦄, i < j → A i j = 0
    intro i j hij
    simp [A, hstrict i j (le_of_lt hij), Matrix.diagonal_apply_ne _ (ne_of_lt hij)]
  refine ⟨lower_folded hA hmono hearly, ?_, hasOrder_iff_folded
    (respects_literal D γ π keep hkeep hrows) b p⟩
  intro i
  rw [diag_folded hA hkeep hearly]
  simp [A, hstrict (keep i) (keep i) le_rfl]

end Ordered

/-- Physical indexing for the fixed-one continuation: keep the old
prefix and the later fresh rows, remove a contiguous copied head. -/
def keepHead (old copies fresh : ℕ) (i : Fin (old+fresh)) :
    Fin (old+copies+fresh) :=
  ⟨if i.val < old then i.val else i.val+copies, by
    split <;> have := i.isLt <;> omega⟩

/-- The removed head slots redirect to specified donors in the old prefix. -/
def redirectHead {old copies fresh : ℕ} (donors : Fin copies → Fin old)
    (i : Fin (old+copies+fresh)) : Fin (old+fresh) :=
  if h : i.val < old then ⟨i.val, by omega⟩
  else if h' : i.val < old+copies then
    ⟨(donors ⟨i.val-old, by omega⟩).val, by have := (donors ⟨i.val-old, by omega⟩).isLt; omega⟩
  else ⟨i.val-copies, by have := i.isLt; omega⟩

theorem keepHead_mono (old copies fresh : ℕ) : StrictMono (keepHead old copies fresh) := by
  intro i j hij
  change (if i.val < old then i.val else i.val+copies) <
    (if j.val < old then j.val else j.val+copies)
  have h : i.val < j.val := hij
  split <;> split <;> omega

theorem redirect_keepHead {old copies fresh : ℕ} (donors : Fin copies → Fin old)
    (i : Fin (old+fresh)) :
    redirectHead (fresh := fresh) donors (keepHead old copies fresh i) = i := by
  apply Fin.ext
  unfold redirectHead keepHead
  by_cases h : i.val < old
  · simp [h]
  · have h' : ¬ i.val + copies < old := by omega
    have h'' : ¬ i.val + copies < old+copies := by omega
    simp [h, h', h'']

theorem keepHead_early {old copies fresh : ℕ} (donors : Fin copies → Fin old)
    (i : Fin (old+copies+fresh)) :
    keepHead old copies fresh (redirectHead donors i) ≤ i := by
  show (keepHead old copies fresh (redirectHead donors i)).val ≤ i.val
  by_cases h : i.val < old
  · simp [redirectHead, keepHead, h]
  · by_cases h' : i.val < old+copies
    · have hg : i.val-old < copies := by omega
      have hd := (donors ⟨i.val-old, hg⟩).isLt
      simp [redirectHead, keepHead, h, h', hd]
      omega
    · have hg : ¬ i.val-copies < old := by omega
      simp [redirectHead, keepHead, h, h', hg]
      omega

/-- The exact physical quotient when all copied donor rows occur as
the first head block, followed by genuinely fresh chronological rows. -/
theorem copiedHead_merge {old copies fresh : ℕ} {K : Type*} [CommSemiring K]
    (donors : Fin copies → Fin old)
    (D : Matrix (Fin (old+copies+fresh)) (Fin (old+copies+fresh)) K) (γ : K)
    (hrows : ∀ i j, D i j = D (keepHead old copies fresh (redirectHead donors i)) j)
    (hstrict : ∀ i j, i ≤ j → D i j = 0)
    (b : Fin (old+copies+fresh) → K) (p : ℕ) :
    let A := D + Matrix.diagonal (fun _ => γ)
    let A' := foldedMatrix (redirectHead donors) (keepHead old copies fresh) A
    A'.IsLowerTriangular ∧ (∀ i, A' i i = γ) ∧
      (HasOrder p A b ↔ HasOrder p A' (foldedWeights (redirectHead donors) b)) :=
  strictSDIRK_merge D γ (redirectHead donors) (keepHead old copies fresh)
    (redirect_keepHead donors) (keepHead_mono old copies fresh)
    (keepHead_early donors) hrows hstrict b p

#print axioms strictSDIRK_merge
#print axioms keepHead_early
end RKResearch.Certified.CausalStageMerge
