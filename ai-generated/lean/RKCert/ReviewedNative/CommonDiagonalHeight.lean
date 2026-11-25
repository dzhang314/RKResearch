module

public import RKCert.ReviewedNative.FiniteRootedSeriesCertificate
import Mathlib.Data.Matrix.Block
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! Joint height and order bounds for the literal native stage columns.
The shallow depth argument uses subtraction, but no division. -/
namespace RKResearch.FiniteSeries

open RKResearch FiniteRootedTree RKResearch.Certified.Graded
open scoped Classical FiniteRootedTree Matrix

/-- Height counts edges, so the leaf has height zero. -/
@[simp] def treeHeight : FiniteRootedTree → ℕ
  | .leaf => 0
  | .butcherProduct base branch => max (treeHeight base) (treeHeight branch + 1)

theorem treeHeight_unary (t : FiniteRootedTree) :
    treeHeight (.leaf ◂ t) = treeHeight t + 1 := by
  change max 0 (treeHeight t + 1) = treeHeight t + 1
  exact max_eq_right (Nat.zero_le _)

theorem treeHeight_rootedSum (t u : FiniteRootedTree) :
    treeHeight (t # u) = max (treeHeight t) (treeHeight u) := by
  induction u with
  | leaf =>
    simpa only [rootedSum, treeHeight] using
      (max_eq_left (Nat.zero_le (treeHeight t))).symm
  | butcherProduct base branch ih _ =>
    simp only [rootedSum, treeHeight, ih, max_assoc]

private theorem unary_order_nat (t : FiniteRootedTree) :
    ((.leaf ◂ t).order : ℕ) = (t.order : ℕ) + 1 := by
  have hu := treeGrade_succ (.leaf ◂ t)
  have ht := treeGrade_succ t
  rw [treeGrade_unary] at hu
  omega

private theorem rootedSum_order_nat (t u : FiniteRootedTree) :
    ((t # u).order : ℕ) + 1 = (t.order : ℕ) + (u.order : ℕ) := by
  have hu := treeGrade_succ (t # u)
  have ht := treeGrade_succ t
  have hv := treeGrade_succ u
  rw [treeGrade_rootedSum] at hu
  omega

private theorem graft_treeGrade (t u : FiniteRootedTree) :
    treeGrade (t ◂ u) = treeGrade t + (treeGrade u + 1) := by
  change treeGrade (t # (.leaf ◂ u)) = _
  rw [treeGrade_rootedSum, treeGrade_unary]

section Columns

variable {ι R : Type*} [Fintype ι] [CommSemiring R]
variable (A : Matrix ι ι R)

/-- Span of raw literal columns satisfying both bounds simultaneously. -/
def heightOrderSpace (h p : ℕ) : Submodule R (ι → R) :=
  Submodule.span R {v | ∃ t : FiniteRootedTree,
    treeHeight t ≤ h ∧ (t.order : ℕ) ≤ p ∧ v = Φ t A}

theorem Φ_mem_heightOrderSpace (t : FiniteRootedTree) {h p : ℕ}
    (height : treeHeight t ≤ h) (ord : (t.order : ℕ) ≤ p) :
    Φ t A ∈ heightOrderSpace A h p :=
  Submodule.subset_span ⟨t, height, ord, rfl⟩

theorem heightOrderSpace_mono {h h' p p' : ℕ}
    (height : h ≤ h') (ord : p ≤ p') :
    heightOrderSpace A h p ≤ heightOrderSpace A h' p' := by
  apply Submodule.span_le.mpr
  rintro _ ⟨t, ht, pt, rfl⟩
  exact Φ_mem_heightOrderSpace A t (ht.trans height) (pt.trans ord)

theorem mat_mem_heightOrderSpace {h p : ℕ} {v : ι → R}
    (hv : v ∈ heightOrderSpace A h p) :
    mat A v ∈ heightOrderSpace A (h+1) (p+1) := by
  have closed : heightOrderSpace A h p ≤ (heightOrderSpace A (h+1) (p+1)).comap (mat A) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨t, ht, pt, rfl⟩
    change mat A (Φ t A) ∈ heightOrderSpace A (h+1) (p+1)
    have hm := Φ_mem_heightOrderSpace A (.leaf ◂ t)
      ((treeHeight_unary t).trans_le (Nat.add_le_add_right ht 1))
      ((unary_order_nat t).trans_le (Nat.add_le_add_right pt 1))
    simpa only [Φ, one_mul, mat_apply] using hm
  exact closed hv

theorem mul_mem_heightOrderSpace {h p q : ℕ} {v w : ι → R}
    (hv : v ∈ heightOrderSpace A h p) (hw : w ∈ heightOrderSpace A h q) :
    v * w ∈ heightOrderSpace A h (p+q-1) := by
  rw [← LinearMap.mul_apply' (R:=R)]
  apply LinearMap.BilinMap.apply_apply_mem_of_mem_span _ _ _
    (LinearMap.mul R (ι → R)) _ _ _ hv hw
  rintro _ ⟨t, ht, pt, rfl⟩ _ ⟨u, hu, pu, rfl⟩
  rw [LinearMap.mul_apply' (R:=R), ← Φ_rootedSum]
  refine Φ_mem_heightOrderSpace A (t # u)
    ((treeHeight_rootedSum t u).trans_le (max_le_iff.mpr ⟨ht, hu⟩)) ?_
  have c := rootedSum_order_nat t u
  omega

end Columns

section Shallow

variable {ι R : Type*} [Fintype ι] [CommRing R]

/-- Only rows certified as shallow have a common diagonal and decreasing
off-diagonal depth. Rows outside the cutoff are unrestricted. -/
structure ShallowCommonDiagonal (A : Matrix ι ι R) (depth : ι → ℕ)
    (D : ℕ) (γ : R) : Prop where
  diag_eq : ∀ i, depth i ≤ D → A i i = γ
  drop : ∀ i j, depth i ≤ D → i ≠ j → A i j ≠ 0 → depth j < depth i

private theorem mat_eq_with_diagonal_correction (A : Matrix ι ι R) (i : ι) (γ : R)
    (x q : ι → R) (diag : A i i = γ)
    (off : ∀ j, j ≠ i → A i j ≠ 0 → x j = q j) :
    mat A x i = mat A q i + γ * (x i - q i) := by
  have eq : mat A (x-q) i = γ * (x i - q i) := by
    simp only [mat_apply, Matrix.mulVec_apply_eq_sum, Pi.sub_apply]
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
    · rw [diag]
    · intro j _ ne
      by_cases hz : A i j = 0
      · rw [hz, zero_mul]
      · rw [off j ne hz, sub_self, mul_zero]
  have out : mat A x i - mat A q i = γ * (x i - q i) := by
    simpa only [map_sub, Pi.sub_apply] using eq
  exact (sub_eq_iff_eq_add.mp out).trans (add_comm _ _)

private theorem Φ_diagonal_row (A : Matrix ι ι R) (i : ι) (γ : R)
    (diag : A i i = γ) (off : ∀ j, j ≠ i → A i j = 0) (t : FiniteRootedTree) :
    Φ t A i = γ ^ treeGrade t := by
  induction t with
  | leaf => simp only [Φ, Pi.one_apply, treeGrade_leaf, pow_zero]
  | butcherProduct base branch ihBase ihBranch =>
    have act := mat_eq_with_diagonal_correction A i γ (Φ branch A) (0 : ι → R) diag
      (fun j ne nz => (nz (off j ne)).elim)
    have act' : mat A (Φ branch A) i = γ * Φ branch A i := by
      simpa only [map_zero, Pi.zero_apply, sub_zero, zero_add] using act
    change Φ base A i * mat A (Φ branch A) i = _
    rw [act', ihBase, ihBranch, graft_treeGrade, pow_add, pow_succ]
    ac_rfl

/-- Each raw column agrees on the shallow coordinates with a combination
of trees of bounded height and of no greater literal order. -/
theorem heightOrderSpace_matches_shallow {A : Matrix ι ι R} {depth : ι → ℕ}
    {D h : ℕ} {γ : R} (hA : ShallowCommonDiagonal A depth D γ)
    (pay : h ≤ D) (t : FiniteRootedTree) :
    ∃ v ∈ heightOrderSpace A h (t.order : ℕ),
      ∀ i, depth i ≤ h → v i = Φ t A i := by
  have build : ∀ k : ℕ, k ≤ D → ∀ u : FiniteRootedTree,
      ∃ v ∈ heightOrderSpace A k (u.order : ℕ),
        ∀ i, depth i ≤ k → v i = Φ u A i := by
    intro k
    induction k with
    | zero =>
      intro hD u
      refine ⟨(γ ^ treeGrade u) • Φ .leaf A, ?_, ?_⟩
      · apply (heightOrderSpace A 0 (u.order : ℕ)).smul_mem
        have leafPaid : ((FiniteRootedTree.leaf).order : ℕ) ≤ (u.order : ℕ) :=
          Nat.succ_le_of_lt u.order.pos
        exact Φ_mem_heightOrderSpace A .leaf (Nat.le_refl 0) leafPaid
      · intro i hi
        have shallow : depth i ≤ D := hi.trans hD
        have off (j : ι) (ne : j ≠ i) : A i j = 0 := by
          by_contra nz
          have lower := hA.drop i j shallow (fun e => ne e.symm) nz
          omega
        simpa only [Pi.smul_apply, smul_eq_mul, Φ, Pi.one_apply, mul_one] using
          (Φ_diagonal_row A i γ (hA.diag_eq i shallow) off u).symm
    | succ k ih =>
      intro hD u
      induction u with
      | leaf =>
        exact ⟨Φ .leaf A, Φ_mem_heightOrderSpace A .leaf (Nat.zero_le _) le_rfl,
          fun _ _ => rfl⟩
      | butcherProduct base branch ihBase ihBranch =>
        obtain ⟨x, hx, eqx⟩ := ihBase
        obtain ⟨y, hy, eqy⟩ := ihBranch
        obtain ⟨q, hq, eqq⟩ := ih ((Nat.le_succ k).trans hD) branch
        let z : ι → R := mat A q + γ • (y-q)
        let V := heightOrderSpace A (k+1) ((branch.order : ℕ)+1)
        have ha : mat A q ∈ V := mat_mem_heightOrderSpace A hq
        have hy' : y ∈ V := heightOrderSpace_mono A le_rfl (Nat.le_succ _) hy
        have hq' : q ∈ V := heightOrderSpace_mono A (Nat.le_succ k) (Nat.le_succ _) hq
        have hz : z ∈ V := V.add_mem ha (V.smul_mem _ (V.sub_mem hy' hq'))
        refine ⟨x*z, ?_, ?_⟩
        · have inside := mul_mem_heightOrderSpace A hx hz
          have count : (base.order : ℕ) + ((branch.order : ℕ)+1)-1 =
              ((base ◂ branch).order : ℕ) := by
            simp only [order, PNat.add_coe]
            omega
          simpa only [count] using inside
        · intro i hi
          have shallow : depth i ≤ D := hi.trans hD
          have off (j : ι) (ne : j ≠ i) (nz : A i j ≠ 0) : Φ branch A j = q j := by
            have lower := hA.drop i j shallow (fun e => ne e.symm) nz
            exact (eqq j (by omega)).symm
          have act := mat_eq_with_diagonal_correction A i γ (Φ branch A) q (hA.diag_eq i shallow) off
          have ez : z i = mat A (Φ branch A) i := by
            simp only [z, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
            rw [eqy i hi, act]
          change x i * z i = Φ base A i * (A *ᵥ Φ branch A) i
          rw [eqx i hi, ez, mat_apply]
  exact build h pay t

/-- Checking every literal raw output through an order bound is equivalent
to checking only those trees within the certified height cutoff. -/
theorem series_zero_through_order_iff_height {A : Matrix ι ι R} {w : ι → R}
    {depth : ι → ℕ} {D : ℕ} {γ : R} (hA : ShallowCommonDiagonal A depth D γ)
    (support : ∀ i, w i ≠ 0 → depth i ≤ D) (p : ℕ) :
    (∀ t : FiniteRootedTree, (t.order : ℕ) ≤ p → w ⬝ᵥ Φ t A = 0) ↔
      (∀ t : FiniteRootedTree, treeHeight t ≤ D → (t.order : ℕ) ≤ p → w ⬝ᵥ Φ t A = 0) := by
  constructor
  · intro all t _ ht
    exact all t ht
  · intro paid t ht
    obtain ⟨v, hv, read⟩ := heightOrderSpace_matches_shallow hA (le_rfl : D ≤ D) t
    have kill : heightOrderSpace A D p ≤ (row w).ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨u, uh, up, rfl⟩
      change w ⬝ᵥ Φ u A = 0
      exact paid u uh up
    have zero := kill (heightOrderSpace_mono A le_rfl ht hv)
    have equal : w ⬝ᵥ v = w ⬝ᵥ Φ t A := by
      simp only [dotProduct]
      apply Finset.sum_congr rfl
      intro i _
      by_cases off : w i = 0
      · simp only [off, zero_mul]
      · rw [read i (support i off)]
    rw [← equal]
    change row w v = 0 at zero
    simpa only [row_apply] using zero

end Shallow

section Comparison

variable {ι κ R : Type*} [Fintype ι] [Fintype κ] [CommRing R]

private theorem Φ_blocks (A : Matrix ι ι R) (B : Matrix κ κ R) (t : FiniteRootedTree) :
    Φ t (Matrix.fromBlocks A 0 0 B) = Sum.elim (Φ t A) (Φ t B) := by
  induction t with
  | leaf =>
    funext i
    cases i <;> rfl
  | butcherProduct base branch ihBase ihBranch =>
    simp only [Φ, ihBase, ihBranch, Matrix.fromBlocks_mulVec]
    funext i
    cases i <;> simp [Function.comp_def]

private theorem block_readout (A : Matrix ι ι R) (B : Matrix κ κ R)
    (b : ι → R) (d : κ → R) (t : FiniteRootedTree) :
    Sum.elim b (fun j => -d j) ⬝ᵥ Φ t (Matrix.fromBlocks A 0 0 B) =
      (b ⬝ᵥ Φ t A) - (d ⬝ᵥ Φ t B) := by
  rw [Φ_blocks, Matrix.dotProduct_block]
  change (b ⬝ᵥ Φ t A) + ((-d) ⬝ᵥ Φ t B) = (b ⬝ᵥ Φ t A) - (d ⬝ᵥ Φ t B)
  rw [neg_dotProduct, sub_eq_add_neg]

/-- Equality of two literal rooted series through any fixed order is
equivalent to equality through that order restricted to height at most D. -/
theorem series_equal_through_order_iff_height {A : Matrix ι ι R} {B : Matrix κ κ R}
    {b : ι → R} {d : κ → R} {δA : ι → ℕ} {δB : κ → ℕ} {D : ℕ} {γ : R}
    (hA : ShallowCommonDiagonal A δA D γ) (hB : ShallowCommonDiagonal B δB D γ)
    (sb : ∀ i, b i ≠ 0 → δA i ≤ D) (sd : ∀ j, d j ≠ 0 → δB j ≤ D) (p : ℕ) :
    (∀ t : FiniteRootedTree, (t.order : ℕ) ≤ p → b ⬝ᵥ Φ t A = d ⬝ᵥ Φ t B) ↔
      (∀ t : FiniteRootedTree, treeHeight t ≤ D → (t.order : ℕ) ≤ p →
        b ⬝ᵥ Φ t A = d ⬝ᵥ Φ t B) := by
  let C : Matrix (ι ⊕ κ) (ι ⊕ κ) R := Matrix.fromBlocks A 0 0 B
  let w : ι ⊕ κ → R := Sum.elim b (fun j => -d j)
  let dep : ι ⊕ κ → ℕ := Sum.elim δA δB
  have hC : ShallowCommonDiagonal C dep D γ := by
    constructor
    · intro i hi
      cases i with
      | inl x => exact hA.diag_eq x hi
      | inr y => exact hB.diag_eq y hi
    · intro i j hi ne nz
      cases i with
      | inl x =>
        cases j with
        | inl y => exact hA.drop x y hi (fun e => ne (congrArg Sum.inl e)) nz
        | inr y => exact (nz rfl).elim
      | inr x =>
        cases j with
        | inl y => exact (nz rfl).elim
        | inr y => exact hB.drop x y hi (fun e => ne (congrArg Sum.inr e)) nz
  have live : ∀ i, w i ≠ 0 → dep i ≤ D := by
    intro i hi
    cases i with
    | inl x => exact sb x hi
    | inr y =>
      apply sd y
      intro hz
      apply hi
      change -d y = 0
      rw [hz, neg_zero]
  have literal (t : FiniteRootedTree) : (w ⬝ᵥ Φ t C = 0) ↔ b ⬝ᵥ Φ t A = d ⬝ᵥ Φ t B := by
    change (Sum.elim b (fun j => -d j) ⬝ᵥ Φ t (Matrix.fromBlocks A 0 0 B) = 0) ↔ _
    rw [block_readout, sub_eq_zero]
  constructor
  · intro all t _ ht
    exact all t ht
  · intro small t ht
    apply (literal t).mp
    exact (series_zero_through_order_iff_height hC live p).mpr
      (fun u hu up => (literal u).mpr (small u hu up)) t ht

end Comparison

end RKResearch.FiniteSeries
