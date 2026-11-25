module

public import RKCert.ReviewedNative.ClockOneLiveSuffix
public import RKCert.ReviewedNative.DIRKReverseGrowth
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Native signed contrasts on a constant live-clock closed suffix

All stage rows, clocks, weights, and reverse flags belong to the original
tableau. The upper support constraint uses a local zero first seed, not a
globally zero row or a shifted tableau's order predicate. -/
namespace RKResearch.Certified.Graded.Reverse

open RKResearch
open scoped Matrix

noncomputable section

variable {K : Type*} [Field K] {s p q n : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
variable {u : Fin s} {y : K}

/-- Restriction to the closed suffix, retaining zero-output rows. -/
def constantSuffixRestrict (u : Fin s) :
    (Fin s → K) →ₗ[K] ({i : Fin s // u ≤ i} → K) :=
  LinearMap.pi (fun i => LinearMap.proj i.val)

@[simp] theorem constantSuffixRestrict_apply (u : Fin s) (v : Fin s → K)
    (i : {j : Fin s // u ≤ j}) : constantSuffixRestrict u v i = v i.val := rfl

private abbrev constantSuffixLine (b : Fin s → K) (u : Fin s) :
    Submodule K (Fin s → K) :=
  (K ∙ constantSuffixRestrict u b).comap (constantSuffixRestrict u)

/-- If two original rows agree on the closed suffix, their original
transpose images agree there as well. This retains the diagonal. -/
private theorem constantSuffix_transpose_congr (ha : A.IsLowerTriangular)
    {v w : Fin s → K} (eq : ∀ i, u ≤ i → v i = w i) (i : Fin s) (hi : u ≤ i) :
    mat A.transpose v i = mat A.transpose w i := by
  have sub : v - w ∈ tailZero u :=
    mem_tailZero.mpr (fun j hj => sub_eq_zero.mpr (eq j hj))
  have z := (mem_tailZero.mp (dirk_transpose_tail ha sub)) i hi
  simpa only [map_sub, Pi.sub_apply, sub_eq_zero] using z

private theorem constantSuffix_weight
    (cl : ∀ i, u ≤ i → b i ≠ 0 → reflectedClock A i = y)
    (k : ℕ) (i : Fin s) (hi : u ≤ i) :
    reflectedStageWeight A b k i = y ^ k * b i := by
  change b i * (reflectedClock A i) ^ k = y ^ k * b i
  by_cases z : b i = 0
  · simp [z]
  · rw [cl i hi z, mul_comm]

private theorem constantSuffix_eigen
    (first : firstSeed A b ∈ tailZero u)
    (cl : ∀ i, u ≤ i → b i ≠ 0 → reflectedClock A i = y)
    (i : Fin s) (hi : u ≤ i) :
    mat A.transpose b i = y * b i := by
  have h := (mem_tailZero.mp first) i hi
  change reflectedStageRow A b 0 i = 0 at h
  have w : reflectedStageWeight A b 0 = b := by
    funext j
    simp only [reflectedStageWeight, pow_zero, mul_one]
  rw [reflectedStageRow, w] at h
  simp only [Nat.zero_add, Nat.cast_one, one_smul, Pi.sub_apply,
    sub_eq_zero] at h
  change (A.transpose *ᵥ b) i = y * b i
  rw [h, constantSuffix_weight cl 1 i hi, pow_one]

/-- Exact restriction of each native reflected primitive row. No order
assumption is needed for this coordinate identity. -/
theorem reflectedStageRow_constant_live_suffix (ha : A.IsLowerTriangular)
    (first : firstSeed A b ∈ tailZero u)
    (cl : ∀ i, u ≤ i → b i ≠ 0 → reflectedClock A i = y)
    (k : ℕ) (i : Fin s) (hi : u ≤ i) :
    reflectedStageRow A b k i = ((k : K) * y ^ (k+1)) * b i := by
  have e := constantSuffix_transpose_congr ha
    (w := y ^ k • b) (fun j hj => constantSuffix_weight cl k j hj) i hi
  change ((k+1 : ℕ) : K) * mat A.transpose (reflectedStageWeight A b k) i -
    reflectedStageWeight A b (k+1) i = _
  rw [e, map_smul, Pi.smul_apply, smul_eq_mul, constantSuffix_eigen first cl i hi,
    constantSuffix_weight cl (k+1) i hi, Nat.cast_add, Nat.cast_one, pow_succ]
  ring

/-- Pointwise form of closed-suffix projection into the weight line.
The scalar depends on the row, not on the chosen stage. -/
theorem primitiveBack_constant_live_suffix_scale (ha : A.IsLowerTriangular)
    (first : firstSeed A b ∈ tailZero u)
    (cl : ∀ i, u ≤ i → b i ≠ 0 → reflectedClock A i = y)
    {v : Fin s → K} (hv : v ∈ primitiveBack A b n) :
    ∃ a : K, ∀ i, u ≤ i → v i = a * b i := by
  let U := constantSuffixLine b u
  have inU (w : Fin s → K) :
      w ∈ U ↔ ∃ a : K, ∀ i, u ≤ i → w i = a * b i := by
    change constantSuffixRestrict u w ∈ K ∙ constantSuffixRestrict u b ↔ _
    rw [Submodule.mem_span_singleton]
    constructor
    · rintro ⟨a, e⟩
      exact ⟨a, fun i hi => (congrFun e ⟨i, hi⟩).symm⟩
    · rintro ⟨a, e⟩
      refine ⟨a, funext (fun i => ?_)⟩
      exact (e i.val i.property).symm
  have inc (m : ℕ) : primitiveBack A b m ≤ U := by
    induction m with
    | zero =>
      change (K ∙ firstSeed A b) ≤ U
      exact (Submodule.span_singleton_le_iff_mem _ _).mpr
        ((inU _).mpr ⟨0, fun i hi => by rw [(mem_tailZero.mp first) i hi, zero_mul]⟩)
    | succ m ih =>
      change _ ⊔ _ ⊔ _ ⊔ _ ≤ U
      refine sup_le (sup_le (sup_le ih ?_) ?_) ?_
      · rintro _ ⟨w, hw, rfl⟩
        obtain ⟨a, e⟩ := (inU w).mp (ih hw)
        apply (inU _).mpr
        refine ⟨a * y, fun i hi => ?_⟩
        have same := constantSuffix_transpose_congr ha (w := a • b) e i hi
        rw [same, map_smul, Pi.smul_apply, smul_eq_mul, constantSuffix_eigen first cl i hi,
          mul_assoc]
      · rintro _ ⟨w, hw, rfl⟩
        obtain ⟨a, e⟩ := (inU w).mp (ih hw)
        apply (inU _).mpr
        refine ⟨y * a, fun i hi => ?_⟩
        rw [diag_apply, e i hi]
        by_cases z : b i = 0
        · simp only [z, mul_zero]
        · rw [cl i hi z, mul_assoc]
      · apply Submodule.span_le.mpr
        rintro _ ⟨k, rfl⟩
        exact (inU _).mpr ⟨(k.val : K) * y ^ (k.val+1),
          reflectedStageRow_constant_live_suffix ha first cl k.val⟩
  exact (inU v).mp (inc n hv)

/-- Every actual closed-suffix projection lies on the weight line. -/
theorem primitiveBack_map_constant_suffix_le_line (ha : A.IsLowerTriangular)
    (first : firstSeed A b ∈ tailZero u)
    (cl : ∀ i, u ≤ i → b i ≠ 0 → reflectedClock A i = y) :
    (primitiveBack A b n).map (constantSuffixRestrict u) ≤ K ∙ constantSuffixRestrict u b := by
  rintro _ ⟨v, hv, rfl⟩
  obtain ⟨a, e⟩ := primitiveBack_constant_live_suffix_scale ha first cl hv
  exact Submodule.mem_span_singleton.mpr ⟨a, funext (fun i => (e i.val i.property).symm)⟩

/-- The quadratic native seed generates the entire projected line once
one reverse step is allowed and the common reflected clock is nonzero. -/
theorem primitiveBack_map_constant_suffix_eq_line (ha : A.IsLowerTriangular)
    (first : firstSeed A b ∈ tailZero u)
    (cl : ∀ i, u ≤ i → b i ≠ 0 → reflectedClock A i = y)
    (hn : 1 ≤ n) (hy : y ≠ 0) :
    (primitiveBack A b n).map (constantSuffixRestrict u) = K ∙ constantSuffixRestrict u b := by
  refine le_antisymm (primitiveBack_map_constant_suffix_le_line ha first cl) ?_
  apply (Submodule.span_singleton_le_iff_mem _ _).mpr
  have mem (m : ℕ) : reflectedStageRow A b 1 ∈ primitiveBack A b (m+1) :=
    adjointFlag_credit (monomialCredit A b) m (monomial_mem_credit m 1 (by omega))
  have hn' : n - 1 + 1 = n := by omega
  have hr : reflectedStageRow A b 1 ∈ primitiveBack A b n := hn' ▸ mem (n-1)
  refine Submodule.mem_map.mpr ⟨(y ^ 2)⁻¹ • reflectedStageRow A b 1,
    (primitiveBack A b n).smul_mem _ hr, ?_⟩
  funext i
  simp only [constantSuffixRestrict_apply, Pi.smul_apply, smul_eq_mul,
    reflectedStageRow_constant_live_suffix ha first cl 1 i.val i.property,
    Nat.cast_one, one_mul, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 hy)]

/-- A zero-mass column physically supported on the closed suffix.
For a live-only contrast use the smaller `suffixLiveContrasts` carrier. -/
theorem supported_constant_suffix_contrast_mem_annih (ha : A.IsLowerTriangular)
    (first : firstSeed A b ∈ tailZero u)
    (cl : ∀ i, u ≤ i → b i ≠ 0 → reflectedClock A i = y)
    {v : Fin s → K} (off : ∀ i, ¬ u ≤ i → v i = 0)
    (mass : row b v = 0) : v ∈ annih (primitiveBack A b n) := by
  apply mem_annih.mpr
  intro w hw
  obtain ⟨a, e⟩ := primitiveBack_constant_live_suffix_scale ha first cl hw
  have same : row v w = a * row b v := by
    simp only [row_apply, dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : u ≤ i
    · rw [e i hi]
      ac_rfl
    · simp only [off i hi, zero_mul, mul_zero]
  rw [same, mass, mul_zero]

/-- Original ambient contrast space: exactly the live rows of the cut
are allowed to carry a coordinate, and their signed mass is zero. -/
def suffixLiveContrasts (b : Fin s → K) (u : Fin s) : Submodule K (Fin s → K) where
  carrier := {v | (∀ i, i ∉ suffixLiveStages b u → v i = 0) ∧ row b v = 0}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw
    exact ⟨fun i hi => by simp only [Pi.add_apply, hv.1 i hi, hw.1 i hi, add_zero],
      by simp only [map_add, hv.2, hw.2, add_zero]⟩
  smul_mem' := by
    intro a v hv
    exact ⟨fun i hi => by simp only [Pi.smul_apply, hv.1 i hi, smul_zero],
      by simp only [map_smul, hv.2, smul_zero]⟩

theorem mem_suffixLiveContrasts {v : Fin s → K} :
    v ∈ suffixLiveContrasts b u ↔
      (∀ i, i ∉ suffixLiveStages b u → v i = 0) ∧ row b v = 0 := Iff.rfl

/-- The contrast is already in the annihilator before making any
saturation assumption or spending a tree-order equation. -/
theorem suffixLiveContrasts_le_annih_primitiveBack (ha : A.IsLowerTriangular)
    (first : firstSeed A b ∈ tailZero u)
    (cl : ∀ i, u ≤ i → b i ≠ 0 → reflectedClock A i = y) :
    suffixLiveContrasts b u ≤ annih (primitiveBack A b n) := by
  intro v hv
  obtain ⟨off, mass⟩ := mem_suffixLiveContrasts.mp hv
  exact supported_constant_suffix_contrast_mem_annih ha first cl
    (fun i hi => off i (fun m => hi (mem_suffixLiveStages.mp m).1)) mass

/-- The actual contrast and tree spaces are both in the same original
annihilator under exactly the native reverse payment. -/
theorem suffixLiveContrasts_sup_treeSpace_le_annih_primitiveBack
    (ha : A.IsLowerTriangular) (ho : HasOrder p A b) (pay : q+n+2 ≤ p)
    (first : firstSeed A b ∈ tailZero u)
    (cl : ∀ i, u ≤ i → b i ≠ 0 → reflectedClock A i = y) :
    suffixLiveContrasts b u ⊔ treeSpace A q ≤ annih (primitiveBack A b n) := by
  refine sup_le (suffixLiveContrasts_le_annih_primitiveBack ha first cl) ?_
  have h := annih_antitone (primitiveBack_annih ho q n pay)
  simpa only [annih_annih] using h

/-- The local contrast codimension in its forward intersection is
bounded by the measured reverse slack. No saturation, nonempty live block,
nonzero reflected clock, or product-moment payment is imposed here. -/
theorem suffixLiveContrasts_inter_treeSpace_codim_le_reverse_slack
    (ha : A.IsLowerTriangular) (ho : HasOrder p A b) (pay : q+n+2 ≤ p)
    (first : firstSeed A b ∈ tailZero u)
    (cl : ∀ i, u ≤ i → b i ≠ 0 → reflectedClock A i = y) :
    Module.finrank K (suffixLiveContrasts b u) +
        Module.finrank K (treeSpace A q) + Module.finrank K (primitiveBack A b n) ≤
      s + Module.finrank K (↥(suffixLiveContrasts b u ⊓ treeSpace A q : Submodule K (Fin s → K))) := by
  have h := Submodule.finrank_mono
    (suffixLiveContrasts_sup_treeSpace_le_annih_primitiveBack ha ho pay first cl)
  have localDim := Submodule.finrank_sup_add_finrank_inf_eq
    (suffixLiveContrasts b u) (treeSpace A q)
  have reverseDim := finrank_annih (primitiveBack A b n)
  rw [Fintype.card_fin] at reverseDim
  omega


end
end RKResearch.Certified.Graded.Reverse
