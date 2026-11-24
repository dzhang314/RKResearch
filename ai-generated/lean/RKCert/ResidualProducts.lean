module

public import RKCert.RootCuts

@[expose] public section

/-!
# Equivalent product tests for the stage residuals

A generator is `c^k ⊙ Q(t₁) ⊙ ⋯ ⊙ Q(tₘ)` with at least one residual. Its
stage degree is `k + ∑ |tᵢ|`; pairing it with the output costs one more vertex.
Expanding one residual in a mixed test replaces it by a difference of two tree
weights. Expanding one branch in the opposite direction gives a residual and a
pure power of the nodes. Both expansions preserve the vertex budget.
-/

namespace RKCert

namespace Tree

/-- Total vertex count of the branches in a list (does not include a common root). -/
def totalOrder : List Tree → ℕ
  | [] => 0
  | t :: ts => t.order + totalOrder ts

end Tree

variable {K : Type*} [Field K] {s : ℕ}

/-- Pointwise product of the stage residuals for the indexed list of branches. -/
def residualProduct (A : Fin s → Fin s → K) : List Tree → Fin s → K
  | [], _ => 1
  | t :: ts, i => stageResidual A t i * residualProduct A ts i

/-- Intermediate test with some residual factors and an arbitrary tree-weight partner. -/
def mixedResidualWeight (A : Fin s → Fin s → K) (b : Fin s → K) (ts : List Tree)
    (u : Tree) : K :=
  ∑ i, b i * (residualProduct A ts i * stageWeight A u i)

@[simp] theorem mixedResidualWeight_singleton (A : Fin s → Fin s → K) (b : Fin s → K)
    (t u : Tree) : mixedResidualWeight A b [t] u = rootCutPair A b t u := by
  simp [mixedResidualWeight, residualProduct, rootCutPair]

/-- Expand one residual into a genuine branch minus its replacement by leaves.
The residuals in `ts` and the partner `u` may be arbitrary. -/
theorem mixedResidualWeight_cons (A : Fin s → Fin s → K) (b : Fin s → K)
    (t : Tree) (ts : List Tree) (u : Tree) :
    mixedResidualWeight A b (t :: ts) u =
      mixedResidualWeight A b ts (.attach t u) -
        mixedResidualWeight A b ts (Tree.addLeaves t.order u) / (t.density : K) := by
  simp only [mixedResidualWeight, residualProduct, div_eq_mul_inv, Finset.sum_mul,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = (b i * residualProduct A ts i) * (stageResidual A t i * stageWeight A u i) := by ac_rfl
    _ = _ := by
      rw [← rootCut_stage, mul_sub, div_eq_mul_inv]
      ac_rfl

/-- Sliding leading leaves behind one branch does not change a mixed test. -/
theorem mixedResidualWeight_slideLeaves (A : Fin s → Fin s → K) (b : Fin s → K)
    (ts : List Tree) (n : ℕ) (t u : Tree) :
    mixedResidualWeight A b ts (Tree.addLeaves n (.attach t u)) =
      mixedResidualWeight A b ts (.attach t (Tree.addLeaves n u)) := by
  unfold mixedResidualWeight
  apply Finset.sum_congr rfl
  intro i _
  rw [stageWeight_addLeaves]
  simp only [stageWeight, stageWeight_addLeaves]
  ac_rfl

/-- All pure residual generators with at least one factor and total vertex cost at most `p`.
No basis, independence, or uniqueness of scalar profiles is assumed. -/
def HasResidualProductTests (A : Fin s → Fin s → K) (b : Fin s → K) (p : ℕ) : Prop :=
  ∀ (k : ℕ) (ts : List Tree), ts ≠ [] → k + Tree.totalOrder ts + 1 ≤ p →
    (∑ i, b i * (residualProduct A ts i * nodes A i ^ k)) = 0

variable [CharZero K]

/-- Full tree order annihilates every mixed test containing a residual, up to its joint budget. -/
theorem mixedResidualWeight_eq_zero_of_treeOrder {A : Fin s → Fin s → K} {b : Fin s → K}
    {p : ℕ} (h : HasTreeOrderAtLeast A b p) (ts : List Tree) (u : Tree)
    (hne : ts ≠ []) (hu : Tree.totalOrder ts + u.order ≤ p) :
    mixedResidualWeight A b ts u = 0 := by
  induction ts generalizing u with
  | nil => contradiction
  | cons t ts ih =>
    cases ts with
    | nil =>
      rw [mixedResidualWeight_singleton]
      exact rootCutPair_eq_zero_of_treeOrder h t u (by simpa [Tree.totalOrder] using hu)
    | cons v vs =>
      rw [mixedResidualWeight_cons]
      have h₁ := ih (.attach t u) (by simp) (by
        simp only [Tree.totalOrder, Tree.order] at *
        omega)
      have h₂ := ih (Tree.addLeaves t.order u) (by simp) (by
        simp only [Tree.totalOrder, Tree.order_addLeaves] at *
        omega)
      rw [h₁, h₂, zero_div, sub_zero]

/-- Full classical tree order iff quadrature and every product of one or more
stage residuals against any admissible monomial. This is a test with *products*;
testing only one residual against monomials is not sufficient. -/
theorem hasTreeOrderAtLeast_iff_residualProductTests
    (A : Fin s → Fin s → K) (b : Fin s → K) (p : ℕ) :
    HasTreeOrderAtLeast A b p ↔ HasMomentsThrough A b p ∧ HasResidualProductTests A b p := by
  constructor
  · intro h
    refine ⟨hasMomentsThrough_of_treeOrder h, ?_⟩
    intro k ts hne hu
    have hbudget : Tree.totalOrder ts + (Tree.bush k).order ≤ p := by
      rw [Tree.order_bush]; omega
    simpa only [mixedResidualWeight, stageWeight_bush] using
      mixedResidualWeight_eq_zero_of_treeOrder h ts (Tree.bush k) hne hbudget
  rintro ⟨hm, hp⟩
  refine (hasTreeOrderAtLeast_iff_rootCutTests A b p).mpr ⟨hm, ?_⟩
  have hmix (u : Tree) (k : ℕ) (ts : List Tree) (hne : ts ≠ [])
      (hdeg : k + Tree.totalOrder ts + u.order ≤ p) :
      mixedResidualWeight A b ts (Tree.addLeaves k u) = 0 := by
    induction u generalizing k ts with
    | leaf =>
      change mixedResidualWeight A b ts (Tree.bush k) = 0
      simpa only [mixedResidualWeight, stageWeight_bush] using hp k ts hne hdeg
    | attach v r _ ihr =>
      rw [mixedResidualWeight_slideLeaves]
      have heq := mixedResidualWeight_cons A b v ts (Tree.addLeaves k r)
      rw [← Tree.addLeaves_add] at heq
      rw [sub_eq_iff_eq_add.mp heq.symm]
      have h₁ := ihr k (v :: ts) (by simp) (by
        simp only [Tree.totalOrder, Tree.order] at *
        omega)
      have h₂ := ihr (v.order + k) ts hne (by
        rw [Tree.order] at hdeg
        omega)
      rw [h₁, h₂, zero_div, add_zero]
  intro t u _ htu
  have hx := hmix u 0 [t] (by simp) (by simpa [Tree.totalOrder] using htu)
  simpa only [Tree.addLeaves, mixedResidualWeight_singleton] using hx

end RKCert
