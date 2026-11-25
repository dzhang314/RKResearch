module

public import RKCert.ReviewedNative.GradedProducts
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! A finite marked-span certificate for literal rooted outputs.
No particular basis selection or decision procedure is assumed. -/
namespace RKResearch.FiniteSeries

open RKResearch FiniteRootedTree RKResearch.Certified.Graded
open scoped Classical FiniteRootedTree Matrix

/-- The grade of a literal reviewed tree is its positive order minus one. -/
abbrev treeGrade (t : FiniteRootedTree) : ℕ := (t.order : ℕ) - 1

@[simp] theorem treeGrade_leaf : treeGrade (.leaf : FiniteRootedTree) = 0 := rfl

theorem treeGrade_succ (t : FiniteRootedTree) : treeGrade t + 1 = (t.order : ℕ) := by
  have positive : 0 < (t.order : ℕ) := t.order.pos
  change (t.order : ℕ) - 1 + 1 = (t.order : ℕ)
  omega

private theorem treeGrade_butcherProduct (t u : FiniteRootedTree) :
    treeGrade (t ◂ u) = treeGrade t + (treeGrade u + 1) := by
  have whole := treeGrade_succ (t ◂ u)
  have left := treeGrade_succ t
  have right := treeGrade_succ u
  have add : ((t ◂ u).order : ℕ) = (t.order : ℕ) + (u.order : ℕ) := by
    simp only [order, PNat.add_coe]
  omega

theorem treeGrade_unary (t : FiniteRootedTree) :
    treeGrade (.leaf ◂ t) = treeGrade t + 1 := by
  simpa only [treeGrade_leaf, zero_add] using treeGrade_butcherProduct .leaf t

theorem treeGrade_rootedSum (t u : FiniteRootedTree) :
    treeGrade (t # u) = treeGrade t + treeGrade u := by
  induction u with
  | leaf => simp only [rootedSum, treeGrade_leaf, Nat.add_zero]
  | butcherProduct base branch ih _ =>
    simp only [rootedSum, treeGrade_butcherProduct, ih, Nat.add_assoc]

variable {ι R : Type*} [Fintype ι] [CommSemiring R]
variable (A : Matrix ι ι R) (marks : List FiniteRootedTree)

/-- The span of the supplied literal columns within a particular grade. -/
def markSpan (q : ℕ) : Submodule R (ι → R) :=
  Submodule.span R {v | ∃ t : FiniteRootedTree, t ∈ marks ∧ treeGrade t ≤ q ∧ v = Φ t A}

/-- Only leaf, unary and merged marks of grade strictly below the cut
need membership certificates, each at its own grade. -/
structure ClosedBelow (cut : ℕ) : Prop where
  leaf_mem : 0 < cut → Φ .leaf A ∈ markSpan A marks 0
  unary_mem : ∀ t ∈ marks, treeGrade t + 1 < cut →
    Φ (.leaf ◂ t) A ∈ markSpan A marks (treeGrade t + 1)
  merge_mem : ∀ t ∈ marks, ∀ u ∈ marks, treeGrade t + treeGrade u < cut →
    Φ (t # u) A ∈ markSpan A marks (treeGrade t + treeGrade u)

private theorem markSpan_mono {m n : ℕ} (le : m ≤ n) : markSpan A marks m ≤ markSpan A marks n := by
  apply Submodule.span_le.mpr
  rintro _ ⟨t, inMarks, budget, rfl⟩
  exact Submodule.subset_span ⟨t, inMarks, budget.trans le, rfl⟩

private theorem unary_markSpan {cut m : ℕ} (h : ClosedBelow A marks cut)
    (pay : m + 1 < cut) {v : ι → R} (hv : v ∈ markSpan A marks m) :
    mat A v ∈ markSpan A marks (m + 1) := by
  have closed : markSpan A marks m ≤ (markSpan A marks (m + 1)).comap (mat A) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨t, inMarks, budget, rfl⟩
    change mat A (Φ t A) ∈ markSpan A marks (m + 1)
    have bound : treeGrade t + 1 ≤ m + 1 := Nat.add_le_add_right budget 1
    have hmem := markSpan_mono A marks bound (h.unary_mem t inMarks (lt_of_le_of_lt bound pay))
    simpa only [Φ, one_mul, mat_apply] using hmem
  exact closed hv

private theorem product_markSpan {cut m n : ℕ} (h : ClosedBelow A marks cut)
    (pay : m + n < cut) {v w : ι → R} (hv : v ∈ markSpan A marks m)
    (hw : w ∈ markSpan A marks n) : v * w ∈ markSpan A marks (m + n) := by
  rw [← LinearMap.mul_apply' (R:=R)]
  apply LinearMap.BilinMap.apply_apply_mem_of_mem_span _ _ _
    (LinearMap.mul R (ι → R)) _ _ _ hv hw
  rintro _ ⟨t, tm, tg, rfl⟩ _ ⟨u, um, ug, rfl⟩
  rw [LinearMap.mul_apply' (R:=R), ← Φ_rootedSum]
  have bound : treeGrade t + treeGrade u ≤ m + n := Nat.add_le_add tg ug
  exact markSpan_mono A marks bound (h.merge_mem t tm u um (lt_of_le_of_lt bound pay))

private theorem Φ_mem_markSpan_own_grade {cut : ℕ} (h : ClosedBelow A marks cut)
    (t : FiniteRootedTree) (paid : treeGrade t < cut) :
    Φ t A ∈ markSpan A marks (treeGrade t) := by
  induction t with
  | leaf => exact h.leaf_mem paid
  | butcherProduct base branch ihBase ihBranch =>
    rw [treeGrade_butcherProduct] at paid ⊢
    have basePay : treeGrade base < cut := by omega
    have branchPay : treeGrade branch < cut := by omega
    have unaryPay : treeGrade branch + 1 < cut := by omega
    have act := unary_markSpan A marks h unaryPay (ihBranch branchPay)
    have product := product_markSpan A marks h paid (ihBase basePay) act
    simpa only [Φ, mat_apply] using product

/-- A drained prefix of the marked columns captures every literal stage
column within the corresponding reviewed order budget. -/
theorem markSpan_eq_treeSpace {cut q : ℕ} (h : ClosedBelow A marks cut) (pay : q < cut) :
    markSpan A marks q = treeSpace A q := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨t, _, budget, rfl⟩
    exact Φ_mem_treeSpace A t ((treeGrade_succ t).symm.trans_le (Nat.add_le_add_right budget 1))
  · apply Submodule.span_le.mpr
    rintro _ ⟨t, orderBound, rfl⟩
    have budget : treeGrade t ≤ q := by
      have horder := treeGrade_succ t
      omega
    exact markSpan_mono A marks budget
      (Φ_mem_markSpan_own_grade A marks h t (lt_of_le_of_lt budget pay))

/-- Zero readout on the paid marks is sufficient for the whole strict
prefix. The functional is the unnormalized reviewed scalar output. -/
theorem series_zero_below {cut : ℕ} (h : ClosedBelow A marks cut) (b : ι → R)
    (zero : ∀ u ∈ marks, treeGrade u < cut → b ⬝ᵥ Φ u A = 0)
    (t : FiniteRootedTree) (paid : treeGrade t < cut) : b ⬝ᵥ Φ t A = 0 := by
  have kills : markSpan A marks (treeGrade t) ≤ (row b).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨u, um, budget, rfl⟩
    change b ⬝ᵥ Φ u A = 0
    exact zero u um (lt_of_le_of_lt budget paid)
  have hz := kills (Φ_mem_markSpan_own_grade A marks h t paid)
  change row b (Φ t A) = 0 at hz
  simpa only [row_apply] using hz

/-- A literal nonzero readout and a certified strict prefix prove that
this witness has minimum order. No choice among tied witnesses is asserted. -/
theorem least_distinguishing_order (b : ι → R) (t : FiniteRootedTree)
    (h : ClosedBelow A marks (treeGrade t)) (nz : b ⬝ᵥ Φ t A ≠ 0)
    (zero : ∀ u ∈ marks, treeGrade u < treeGrade t → b ⬝ᵥ Φ u A = 0) :
    (b ⬝ᵥ Φ t A ≠ 0) ∧
      ∀ u : FiniteRootedTree, b ⬝ᵥ Φ u A ≠ 0 → (t.order : ℕ) ≤ (u.order : ℕ) := by
  refine ⟨nz, ?_⟩
  intro u diff
  by_contra bad
  have smaller : treeGrade u < treeGrade t := by
    have ht := treeGrade_succ t
    have hu := treeGrade_succ u
    omega
  exact diff (series_zero_below A marks h b zero u smaller)

/-- A single finite cutoff above the cost of all mark operations is
enough for equality on the entire rooted series. -/
theorem full_series_zero_iff_checked_marks (b : ι → R) {cap : ℕ}
    (h : ClosedBelow A marks (2 * cap + 2))
    (bound : ∀ t ∈ marks, treeGrade t ≤ cap) :
    (∀ t : FiniteRootedTree, b ⬝ᵥ Φ t A = 0) ↔ ∀ t ∈ marks, b ⬝ᵥ Φ t A = 0 := by
  constructor
  · intro zero t _
    exact zero t
  · intro zero t
    have full (cut : ℕ) : ClosedBelow A marks cut := by
      refine ⟨fun _ => h.leaf_mem (by omega), ?_, ?_⟩
      · intro u hu _
        have small := bound u hu
        exact h.unary_mem u hu (by omega)
      · intro u hu v hv _
        have su := bound u hu
        have sv := bound v hv
        exact h.merge_mem u hu v hv (by omega)
    exact series_zero_below A marks (full (treeGrade t + 1)) b
      (fun u hu _ => zero u hu) t (Nat.lt_succ_self _)

end RKResearch.FiniteSeries
