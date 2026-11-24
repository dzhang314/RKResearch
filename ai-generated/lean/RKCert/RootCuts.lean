module

public import RKCert.Field

@[expose] public section

/-!
# Stage residuals and root cuts

Use the row sums of `A` as the abscissae. A cut replaces a branch `t` at the
root by `t.order` leaves. The vertex count is unchanged. No order or triangularity
assumption is needed for the difference-of-errors identity.
-/

namespace RKCert
namespace Tree

/-- Put `n` additional leaves at the root of `u`. -/
def addLeaves : ℕ → Tree → Tree
  | 0, u => u
  | n + 1, u => .attach .leaf (addLeaves n u)

/-- Root with `n` leaf children. -/
def bush (n : ℕ) : Tree := addLeaves n .leaf

@[simp] theorem order_addLeaves (n : ℕ) (u : Tree) :
    (addLeaves n u).order = n + u.order := by
  induction n with
  | zero => simp [addLeaves]
  | succ n ih => simp only [addLeaves, order, ih]; omega

@[simp] theorem childDensityProduct_addLeaves (n : ℕ) (u : Tree) :
    (addLeaves n u).childDensityProduct = u.childDensityProduct := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [addLeaves, childDensityProduct, order, one_mul] using ih

@[simp] theorem density_addLeaves (n : ℕ) (u : Tree) :
    (addLeaves n u).density = (n + u.order) * u.childDensityProduct := by
  simp [density]

@[simp] theorem order_bush (n : ℕ) : (bush n).order = n + 1 := by
  simp [bush, order]

@[simp] theorem density_bush (n : ℕ) : (bush n).density = n + 1 := by
  simp [bush, order, childDensityProduct]

/-- Root-order factors agree before and after a cut. All other factorials agree
except for the factorial of the branch that was cut. -/
theorem density_attach_cut (t u : Tree) :
    (attach t u).density = (addLeaves t.order u).density * t.density := by
  rw [density_addLeaves]
  simp only [density, order, childDensityProduct]
  ac_rfl

/-- Successive batches of root leaves add their vertex counts. -/
theorem addLeaves_add (m n : ℕ) (u : Tree) :
    addLeaves (m + n) u = addLeaves m (addLeaves n u) := by
  induction m with
  | zero => simp [addLeaves]
  | succ m ih => rw [Nat.succ_add]; simp only [addLeaves, ih]

theorem density_slideLeaves (n : ℕ) (t u : Tree) :
    (addLeaves n (.attach t u)).density = (attach t (addLeaves n u)).density := by
  rw [density_addLeaves]
  simp only [density, order, childDensityProduct, order_addLeaves, childDensityProduct_addLeaves]
  ac_rfl

end Tree

variable {K : Type*} {s : ℕ}

section Semiring
variable [CommSemiring K]

/-- Abscissae are internal row sums, not independently supplied data. -/
def nodes (A : Fin s → Fin s → K) (i : Fin s) : K := ∑ j, A i j

theorem stageWeight_addLeaves (A : Fin s → Fin s → K) (n : ℕ) (u : Tree) (i : Fin s) :
    stageWeight A (Tree.addLeaves n u) i = nodes A i ^ n * stageWeight A u i := by
  induction n with
  | zero => simp [Tree.addLeaves]
  | succ n ih =>
    simp only [Tree.addLeaves, stageWeight, mul_one, ih, nodes, pow_succ]
    ac_rfl

theorem stageWeight_bush (A : Fin s → Fin s → K) (n : ℕ) (i : Fin s) :
    stageWeight A (Tree.bush n) i = nodes A i ^ n := by
  simp only [Tree.bush, stageWeight_addLeaves, stageWeight, mul_one]

/-- Scalar quadrature through the constant and all powers with `k+1 ≤ p`. -/
def HasMomentsThrough (A : Fin s → Fin s → K) (b : Fin s → K) (p : ℕ) : Prop :=
  ∀ k : ℕ, k + 1 ≤ p → ((k + 1 : ℕ) : K) * (∑ i, b i * nodes A i ^ k) = 1

theorem hasMomentsThrough_of_treeOrder {A : Fin s → Fin s → K} {b : Fin s → K}
    {p : ℕ} (h : HasTreeOrderAtLeast A b p) : HasMomentsThrough A b p := by
  intro k hk
  simpa only [Tree.density_bush, weight, stageWeight_bush] using
    h (Tree.bush k) (by simpa only [Tree.order_bush] using hk)

end Semiring

section Field
variable [Field K]

/-- Stepanov's stage residual `Q(t) = A Φ_t − c^|t| / γ(t)`, componentwise. -/
def stageResidual (A : Fin s → Fin s → K) (t : Tree) (i : Fin s) : K :=
  (∑ j, A i j * stageWeight A t j) - nodes A i ^ t.order / (t.density : K)

@[simp] theorem stageResidual_leaf (A : Fin s → Fin s → K) (i : Fin s) :
    stageResidual A .leaf i = 0 := by
  simp [stageResidual, Tree.order, Tree.density, Tree.childDensityProduct, stageWeight, nodes]

/-- Test the residual of a single branch against the remaining branches' full
stage weight, not just a monomial in the nodes. -/
def rootCutPair (A : Fin s → Fin s → K) (b : Fin s → K) (t u : Tree) : K :=
  ∑ i, b i * (stageResidual A t i * stageWeight A u i)

/-- Denominator-cleared output error. -/
def treeError (A : Fin s → Fin s → K) (b : Fin s → K) (t : Tree) : K :=
  (t.density : K) * weight A b t - 1

/-- Unconditional identity before pairing with the weights. -/
theorem rootCut_stage (A : Fin s → Fin s → K) (t u : Tree) (i : Fin s) :
    stageWeight A (.attach t u) i -
        stageWeight A (Tree.addLeaves t.order u) i / (t.density : K) =
      stageResidual A t i * stageWeight A u i := by
  simp only [stageWeight, stageWeight_addLeaves, stageResidual, div_eq_mul_inv, sub_mul]
  ac_rfl

/-- The output identity with the cut tree's (possibly nontrivial) denominator. -/
theorem rootCut_weight (A : Fin s → Fin s → K) (b : Fin s → K) (t u : Tree) :
    weight A b (.attach t u) - weight A b (Tree.addLeaves t.order u) / (t.density : K) =
      rootCutPair A b t u := by
  simp only [weight, div_eq_mul_inv, Finset.sum_mul, rootCutPair, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← rootCut_stage]
  simp only [mul_sub, div_eq_mul_inv, mul_assoc]

variable [CharZero K]

/-- Replacing one root branch by leaves changes the normalized output error by
exactly the paired residual times the factorial of the tree *before* cutting. -/
theorem treeError_sub_cut (A : Fin s → Fin s → K) (b : Fin s → K) (t u : Tree) :
    treeError A b (.attach t u) - treeError A b (Tree.addLeaves t.order u) =
      ((Tree.attach t u).density : K) * rootCutPair A b t u := by
  have hden : (t.density : K) ≠ 0 := Nat.cast_ne_zero.mpr t.density_pos.ne'
  rw [← rootCut_weight, mul_sub, treeError, treeError, sub_sub_sub_cancel_right]
  congr 1
  rw [Tree.density_attach_cut, Nat.cast_mul, div_eq_mul_inv]
  symm
  calc
    _ = ((Tree.addLeaves t.order u).density : K) * weight A b (Tree.addLeaves t.order u) *
        ((t.density : K) * (t.density : K)⁻¹) := by ac_rfl
    _ = _ := by rw [mul_inv_cancel₀ hden, mul_one]

omit [CharZero K] in
/-- A cut at a leaf is identically zero and need not be imposed. -/
@[simp] theorem rootCutPair_leaf (A : Fin s → Fin s → K) (b : Fin s → K) (u : Tree) :
    rootCutPair A b .leaf u = 0 := by simp [rootCutPair]

/-- Only a joint vertex budget appears: the total order is `|t|+|u|`. -/
def HasRootCutTests (A : Fin s → Fin s → K) (b : Fin s → K) (p : ℕ) : Prop :=
  ∀ t u : Tree, t ≠ .leaf → t.order + u.order ≤ p → rootCutPair A b t u = 0

/-- Necessity uses the two equal-order trees in the unconditional cut identity. -/
theorem rootCutPair_eq_zero_of_treeOrder {A : Fin s → Fin s → K} {b : Fin s → K}
    {p : ℕ} (h : HasTreeOrderAtLeast A b p) (t u : Tree)
    (hu : t.order + u.order ≤ p) : rootCutPair A b t u = 0 := by
  have hsub := treeError_sub_cut A b t u
  have h₁ := h (.attach t u) hu
  have h₂ := h (Tree.addLeaves t.order u) (by simpa only [Tree.order_addLeaves] using hu)
  rw [treeError, treeError, h₁, h₂, sub_self] at hsub
  exact (mul_eq_zero.mp hsub.symm).resolve_left (Nat.cast_ne_zero.mpr (Tree.attach t u).density_pos.ne')

omit [CharZero K] in
/-- Moving leading root leaves behind one other branch preserves the normalized
weight; this is just commutativity of child factors, not equality of ordered trees. -/
theorem treeError_slideLeaves (A : Fin s → Fin s → K) (b : Fin s → K) (n : ℕ) (t u : Tree) :
    treeError A b (Tree.addLeaves n (.attach t u)) =
      treeError A b (.attach t (Tree.addLeaves n u)) := by
  rw [treeError, treeError, Tree.density_slideLeaves]
  congr 2
  unfold weight
  apply Finset.sum_congr rfl
  intro i _
  rw [stageWeight_addLeaves]
  simp only [stageWeight, stageWeight_addLeaves]
  ac_rfl

/-- Full classical tree order iff bush quadrature and single-branch residual
tests against every allowed stage-weight partner. In the reverse direction,
move root leaves aside and cut the remaining branches one by one. -/
theorem hasTreeOrderAtLeast_iff_rootCutTests
    (A : Fin s → Fin s → K) (b : Fin s → K) (p : ℕ) :
    HasTreeOrderAtLeast A b p ↔ HasMomentsThrough A b p ∧ HasRootCutTests A b p := by
  constructor
  · intro h
    exact ⟨hasMomentsThrough_of_treeOrder h,
      fun t u _ hu => rootCutPair_eq_zero_of_treeOrder h t u hu⟩
  rintro ⟨hm, hq⟩
  have hcut (t u : Tree) (hu : t.order + u.order ≤ p) : rootCutPair A b t u = 0 := by
    by_cases ht : t = .leaf
    · subst t; exact rootCutPair_leaf A b u
    · exact hq t u ht hu
  have hzero (r : Tree) (n : ℕ) (hn : n + r.order ≤ p) :
      treeError A b (Tree.addLeaves n r) = 0 := by
    induction r generalizing n with
    | leaf =>
      change treeError A b (Tree.bush n) = 0
      simp only [treeError, Tree.density_bush, weight, stageWeight_bush, hm n hn, sub_self]
    | attach t u _ ihu =>
      rw [treeError_slideLeaves]
      have ht := treeError_sub_cut A b t (Tree.addLeaves n u)
      have hbound : t.order + (Tree.addLeaves n u).order ≤ p := by
        rw [Tree.order_addLeaves]
        change n + (t.order + u.order) ≤ p at hn
        omega
      rw [hcut _ _ hbound, mul_zero] at ht
      rw [sub_eq_zero.mp ht, ← Tree.addLeaves_add]
      apply ihu
      rw [Tree.order] at hn
      omega
  intro t ht
  exact sub_eq_zero.mp (hzero t 0 (by simpa using ht))

end Field
end RKCert
