module

public import RKCert.RootCuts

@[expose] public section

/-!
# Root cuts without division

Over a commutative semiring the cut test can be written as an equality between
two sums, with no subtraction or inverse. A genuine order condition makes its
own tree factorial a unit: the output weight supplies an inverse. Consequently
the full equivalence needs no a priori regularity assumption on integers.

In a commutative ring the balanced test is precisely output annihilation of the
scaled residual `γ(t) AΦ(t) − c^|t|` paired with the partner weight. Even with
zero divisors, no cancellation by an unproved nonzero scalar enters the proof.
-/

namespace RKCert

variable {K : Type*} {s : ℕ}

section Semiring
variable [CommSemiring K]

/-- In a quadrature of order `p`, each positive integer through `p` is a unit. -/
theorem isUnit_nat_of_moments {A : Fin s → Fin s → K} {b : Fin s → K} {p n : ℕ}
    (h : HasMomentsThrough A b p) (hn : 0 < n) (hnp : n ≤ p) : IsUnit (n : K) := by
  cases n with
  | zero => exact False.elim (Nat.lt_irrefl _ hn)
  | succ n => exact IsUnit.of_mul_eq_one _ (h n hnp)

/-- The factorial of `p` is a unit as soon as the cleared order conditions hold.
For `p=0` this says only that `1` is a unit. -/
theorem factorial_isUnit_of_treeOrder {A : Fin s → Fin s → K} {b : Fin s → K}
    {p : ℕ} (h : HasTreeOrderAtLeast A b p) : IsUnit (p.factorial : K) := by
  cases p with
  | zero => simp
  | succ n => exact IsUnit.of_mul_eq_one _ (chain_condition h (n := n) le_rfl)

/-- The factorial index `p!` controls precisely the units needed for all trees through `p`. -/
theorem factorial_isUnit_iff_treeDensities (p : ℕ) :
    IsUnit (p.factorial : K) ↔ ∀ t : Tree, t.order ≤ p → IsUnit (t.density : K) := by
  constructor
  · intro hfac
    have hnat (n : ℕ) (hpos : 0 < n) (hle : n ≤ p) : IsUnit (n : K) := by
      exact isUnit_iff_dvd_one.mpr ((Nat.cast_dvd_cast (Nat.dvd_factorial hpos hle)).trans
        (isUnit_iff_dvd_one.mp hfac))
    have hchild (t : Tree) (ht : t.order ≤ p) : IsUnit (t.childDensityProduct : K) := by
      induction t with
      | leaf => simp [Tree.childDensityProduct]
      | attach t u iht ihu =>
        change t.order + u.order ≤ p at ht
        simp only [Tree.childDensityProduct, Nat.cast_mul]
        exact ((hnat t.order t.order_pos (by omega)).mul (iht (by omega))).mul (ihu (by omega))
    intro t ht
    rw [Tree.density, Nat.cast_mul]
    exact (hnat t.order t.order_pos ht).mul (hchild t ht)
  · intro h
    cases p with
    | zero => simp
    | succ n =>
      simpa only [Tree.density_chain] using h (Tree.chain n) (by simp only [Tree.order_chain, le_refl])

/-- The moments alone make every required tree factorial a unit. -/
theorem treeDensity_isUnit_of_moments {A : Fin s → Fin s → K} {b : Fin s → K} {p : ℕ}
    (h : HasMomentsThrough A b p) (t : Tree) (ht : t.order ≤ p) : IsUnit (t.density : K) := by
  have hfac (n : ℕ) (hn : n ≤ p) : IsUnit (n.factorial : K) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.factorial_succ, Nat.cast_mul]
      exact (isUnit_nat_of_moments h (Nat.zero_lt_succ n) hn).mul (ih (by omega))
  exact (factorial_isUnit_iff_treeDensities p).mp (hfac p le_rfl) t ht

/-- A single root cut, written as a balance between two ordinary weights. -/
def BalancedRootCut (A : Fin s → Fin s → K) (b : Fin s → K) (t u : Tree) : Prop :=
  (t.density : K) * weight A b (.attach t u) = weight A b (Tree.addLeaves t.order u)

/-- Full nontrivial cut tests, with the exact joint order cutoff. -/
def HasBalancedRootCuts (A : Fin s → Fin s → K) (b : Fin s → K) (p : ℕ) : Prop :=
  ∀ t u : Tree, t ≠ .leaf → t.order + u.order ≤ p → BalancedRootCut A b t u

/-- Necessity needs no domain hypothesis: the weight of the cut tree inverts its factorial. -/
theorem balancedRootCut_of_treeOrder {A : Fin s → Fin s → K} {b : Fin s → K} {p : ℕ}
    (h : HasTreeOrderAtLeast A b p) (t u : Tree) (htu : t.order + u.order ≤ p) :
    BalancedRootCut A b t u := by
  have hw := h (Tree.addLeaves t.order u) (by simpa only [Tree.order_addLeaves] using htu)
  have hv := h (.attach t u) htu
  apply (IsUnit.of_mul_eq_one _ hw).mul_left_cancel
  rw [← mul_assoc, ← Nat.cast_mul, ← Tree.density_attach_cut, hv, hw]

/-- Reordering a root branch and an adjacent batch of leaves preserves its output weight. -/
theorem weight_slideLeaves (A : Fin s → Fin s → K) (b : Fin s → K) (n : ℕ) (t u : Tree) :
    weight A b (Tree.addLeaves n (.attach t u)) = weight A b (.attach t (Tree.addLeaves n u)) := by
  unfold weight
  apply Finset.sum_congr rfl
  intro i _
  rw [stageWeight_addLeaves]
  simp only [stageWeight, stageWeight_addLeaves]
  ac_rfl

/-- The division-free root-cut theorem for every commutative semiring. -/
theorem hasTreeOrderAtLeast_iff_balancedRootCuts
    (A : Fin s → Fin s → K) (b : Fin s → K) (p : ℕ) :
    HasTreeOrderAtLeast A b p ↔ HasMomentsThrough A b p ∧ HasBalancedRootCuts A b p := by
  constructor
  · intro h
    exact ⟨hasMomentsThrough_of_treeOrder h, fun t u _ htu => balancedRootCut_of_treeOrder h t u htu⟩
  rintro ⟨hm, hbal⟩
  have hcut (t u : Tree) (htu : t.order + u.order ≤ p) : BalancedRootCut A b t u := by
    by_cases ht : t = .leaf
    · subst t
      simp [BalancedRootCut, Tree.order, Tree.density, Tree.childDensityProduct, Tree.addLeaves]
    · exact hbal t u ht htu
  have hnorm (u : Tree) (n : ℕ) (hdeg : n + u.order ≤ p) :
      ((Tree.addLeaves n u).density : K) * weight A b (Tree.addLeaves n u) = 1 := by
    induction u generalizing n with
    | leaf =>
      change ((Tree.bush n).density : K) * weight A b (Tree.bush n) = 1
      simpa only [Tree.density_bush, weight, stageWeight_bush] using hm n hdeg
    | attach t u _ ihu =>
      change n + (t.order + u.order) ≤ p at hdeg
      have hh := hcut t (Tree.addLeaves n u) (by rw [Tree.order_addLeaves]; omega)
      rw [Tree.density_slideLeaves, weight_slideLeaves, Tree.density_attach_cut, Nat.cast_mul,
        mul_assoc, hh, ← Tree.addLeaves_add]
      exact ihu _ (by omega)
  exact fun t ht => hnorm t 0 (by simpa using ht)

end Semiring

section Ring
variable [CommRing K]

/-- Denominator-free stage residual. Over a field with invertible factorials this is `γ(t) Q(t)`. -/
def scaledStageResidual (A : Fin s → Fin s → K) (t : Tree) (i : Fin s) : K :=
  (t.density : K) * (∑ j, A i j * stageWeight A t j) - nodes A i ^ t.order

/-- Its pairing against the uncut branches. -/
def scaledRootCutPair (A : Fin s → Fin s → K) (b : Fin s → K) (t u : Tree) : K :=
  ∑ i, b i * (scaledStageResidual A t i * stageWeight A u i)

theorem scaledRootCut_stage (A : Fin s → Fin s → K) (t u : Tree) (i : Fin s) :
    scaledStageResidual A t i * stageWeight A u i =
      (t.density : K) * stageWeight A (.attach t u) i - stageWeight A (Tree.addLeaves t.order u) i := by
  simp only [scaledStageResidual, stageWeight, stageWeight_addLeaves, sub_mul, mul_assoc]

theorem scaledRootCutPair_eq (A : Fin s → Fin s → K) (b : Fin s → K) (t u : Tree) :
    scaledRootCutPair A b t u =
      (t.density : K) * weight A b (.attach t u) - weight A b (Tree.addLeaves t.order u) := by
  simp only [scaledRootCutPair, weight, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [scaledRootCut_stage, mul_sub]
  ac_rfl

/-- Subtracting the two normalized outputs exposes the factorial *after* the cut:
the factor of the branch itself is already present in the scaled residual. -/
theorem scaled_normalizedCut_difference (A : Fin s → Fin s → K) (b : Fin s → K)
    (t u : Tree) :
    ((Tree.attach t u).density : K) * weight A b (.attach t u) -
        ((Tree.addLeaves t.order u).density : K) * weight A b (Tree.addLeaves t.order u) =
      ((Tree.addLeaves t.order u).density : K) * scaledRootCutPair A b t u := by
  rw [Tree.density_attach_cut, Nat.cast_mul, mul_assoc, scaledRootCutPair_eq, mul_sub]

/-- All scaled single-residual pairings with an arbitrary tree partner. -/
def HasScaledRootCutTests (A : Fin s → Fin s → K) (b : Fin s → K) (p : ℕ) : Prop :=
  ∀ t u : Tree, t ≠ .leaf → t.order + u.order ≤ p → scaledRootCutPair A b t u = 0

/-- Equivalence over an arbitrary commutative ring, including rings with zero divisors.
If an integer through `p` is not a unit, the moment conditions already fail. -/
theorem hasTreeOrderAtLeast_iff_scaledRootCutTests
    (A : Fin s → Fin s → K) (b : Fin s → K) (p : ℕ) :
    HasTreeOrderAtLeast A b p ↔ HasMomentsThrough A b p ∧ HasScaledRootCutTests A b p := by
  simp only [hasTreeOrderAtLeast_iff_balancedRootCuts, HasBalancedRootCuts, BalancedRootCut,
    HasScaledRootCutTests, scaledRootCutPair_eq, sub_eq_zero]

end Ring
end RKCert
