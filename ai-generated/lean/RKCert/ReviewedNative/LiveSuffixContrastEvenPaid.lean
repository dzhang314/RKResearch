module

public import RKCert.ReviewedNative.LiveSuffixContrastPairingRank
public import RKCert.ReviewedNative.CompensatedRestrictionRank
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Even-paid forward room from native live-suffix contrasts

The measured Gram rank of the actual forward intersection is paid at order
2q into the original degree-q defect quotient. There is no extra ordinary
moment here: the polynomial component has merely a constant trace on the
supported live clock, not a proof of vanishing as an ambient column. -/
namespace RKResearch.Certified.Graded.Reverse

open RKResearch Module
open scoped Matrix BigOperators Classical

noncomputable section

variable {K : Type*} [Field K] {s p q n : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
variable {u : Fin s} {y : K}

/-- The original contrast-tree intersection, regarded as a subspace of
the contrast carrier so that its dual restriction has the correct type. -/
abbrev suffixContrastFront (A : Matrix (Fin s) (Fin s) K) (b : Fin s → K)
    (u : Fin s) (q : ℕ) : Submodule K (suffixLiveContrasts b u) :=
  (treeSpace A q).comap (suffixLiveContrasts b u).subtype

/-- Pair with an actual member of the contrast-tree intersection. -/
abbrev suffixContrastEvenReadout (A : Matrix (Fin s) (Fin s) K) (b : Fin s → K)
    (u : Fin s) (q : ℕ) :
    (Fin s → K) →ₗ[K] Dual K (suffixContrastFront A b u q) :=
  (suffixContrastFront A b u q).dualRestrict.comp
    ((suffixLiveContrasts b u).dualRestrict.comp (suffixSignedPairing b))

/-- The doubly restricted native signed-output pairing. -/
abbrev suffixContrastFrontPairing (A : Matrix (Fin s) (Fin s) K) (b : Fin s → K)
    (u : Fin s) (q : ℕ) :
    suffixContrastFront A b u q →ₗ[K] Dual K (suffixContrastFront A b u q) :=
  (suffixContrastFront A b u q).dualRestrict.comp
    ((suffixContrastPairing b u).domRestrict (suffixContrastFront A b u q))

/-- The genuine preceding defect span and its actual clock image. -/
abbrev suffixContrastLowerClockSpan (A : Matrix (Fin s) (Fin s) K) (q : ℕ) :
    Submodule K (Fin s → K) :=
  zeroSpace A (q-1) ⊔ (zeroSpace A (q-1)).map (diag (nodes A))

private theorem original_clock_eq_on_live_suffix
    (cl : ∀ i, u ≤ i → b i ≠ 0 → reflectedClock A i = y)
    {i : Fin s} (hi : i ∈ suffixLiveStages b u) :
    nodes A i = 1-y := by
  obtain ⟨ui, bi⟩ := mem_suffixLiveStages.mp hi
  have h := cl i ui bi
  change (1 : K)-nodes A i = y at h
  rw [← h, sub_sub_cancel]

private theorem signed_row_scale_on_suffix_support
    {v c z : Fin s → K} (hv : v ∈ suffixLiveContrasts b u) {r : K}
    (agree : ∀ i ∈ suffixLiveStages b u, c i = r) :
    row b ((c * z) * v) = r * row b (z * v) := by
  obtain ⟨off, _⟩ := mem_suffixLiveContrasts.mp hv
  simp only [row_apply, dotProduct, Pi.mul_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ suffixLiveStages b u
  · rw [agree i hi]
    ac_rfl
  · simp only [off i hi, mul_zero]

/-- Original clock polynomials have a constant live-block trace, which is
invisible to the signed contrast. No extra moment is consumed. -/
theorem coeffEval_pair_suffixLiveContrasts_eq_zero
    (cl : ∀ i, u ≤ i → b i ≠ 0 → reflectedClock A i = y)
    (a : Fin (q+1) → K) {v : Fin s → K} (hv : v ∈ suffixLiveContrasts b u) :
    row b (coeffEval A q a * v) = 0 := by
  let t : K := ∑ j : Fin (q+1), a j * (1-y)^j.val
  have same (i : Fin s) (hi : i ∈ suffixLiveStages b u) : coeffEval A q a i = t := by
    simp only [t, coeffEval_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      normTree_clockTree, Pi.pow_apply, original_clock_eq_on_live_suffix cl hi]
  have e := signed_row_scale_on_suffix_support hv (z := (1 : Fin s → K)) same
  rw [mul_one, one_mul, (mem_suffixLiveContrasts.mp hv).2, mul_zero] at e
  exact e

private theorem paid_lower_defect_pair_suffixFront_eq_zero (ho : HasOrder p A b)
    (qpos : 1 ≤ q) (epay : 2*q ≤ p) {f : Fin s → K}
    (hf : f ∈ zeroSpace A (q-1)) {v : Fin s → K} (hv : v ∈ treeSpace A q) :
    row b (f * v) = 0 := by
  have prod : f * v ∈ zeroSpace A (q-1+q) :=
    zeroSpace_mul_treeSpace ho (by omega : q+1 ≤ p) hf hv
  have z : probe A b 0 (f * v) = 0 := probe_zeroSpace (k := 0) ho (by omega) prod
  simpa only [probe, pow_zero, mul_one] using z

/-- Exact even payment: the native pairing on the actual intersection is
represented by the grade-q defect space, and the previous grade plus its
clock image is in the kernel of the very same readout. -/
theorem even_paid_suffix_front_pairing_debit (ho : HasOrder p A b)
    (qpos : 1 ≤ q) (epay : 2*q ≤ p)
    (cl : ∀ i, u ≤ i → b i ≠ 0 → reflectedClock A i = y) :
    finrank K (suffixContrastLowerClockSpan A q) +
      finrank K (suffixContrastFrontPairing A b u q).range ≤ finrank K (zeroSpace A q) := by
  let C := suffixLiveContrasts b u
  let V := suffixContrastFront A b u q
  let U := suffixContrastLowerClockSpan A q
  let F := zeroSpace A q
  let θ := suffixContrastEvenReadout A b u q
  let B := suffixContrastFrontPairing A b u q
  have inc : U ≤ F := by
    refine sup_le (zeroSpace_mono A (by omega)) ?_
    have advance := diag_zeroSpace A (q-1)
    rw [show q-1+1 = q by omega] at advance
    exact Submodule.map_le_iff_le_comap.mpr advance
  have low (f : Fin s → K) (hf : f ∈ zeroSpace A (q-1)) : θ f = 0 := by
    apply LinearMap.ext
    intro v
    change row b (f * v.val.val) = 0
    exact paid_lower_defect_pair_suffixFront_eq_zero ho qpos epay hf v.property
  have clock (f : Fin s → K) (hf : f ∈ zeroSpace A (q-1)) :
      θ (diag (nodes A) f) = 0 := by
    apply LinearMap.ext
    intro v
    change row b ((nodes A * f) * v.val.val) = 0
    have e := signed_row_scale_on_suffix_support v.val.property (z := f)
      (fun _ i => original_clock_eq_on_live_suffix cl i)
    have h : row b (f * v.val.val) = 0 :=
      paid_lower_defect_pair_suffixFront_eq_zero ho qpos epay hf v.property
    rw [e, h, mul_zero]
  have killed : U ≤ LinearMap.ker θ := by
    refine sup_le (fun f hf => LinearMap.mem_ker.mpr (low f hf)) ?_
    rintro _ ⟨f, hf, rfl⟩
    exact LinearMap.mem_ker.mpr (clock f hf)
  have fit : LinearMap.range B ≤ LinearMap.range (θ.domRestrict F) := by
    rintro _ ⟨v, rfl⟩
    have ht : v.val.val ∈ treeSpace A q := v.property
    rw [treeSpace_coeff_sup ho (by omega : q+1 ≤ p)] at ht
    obtain ⟨g, hg, f, hf, e⟩ := Submodule.mem_sup.mp ht
    obtain ⟨a, rfl⟩ := hg
    refine ⟨⟨f, hf⟩, ?_⟩
    apply LinearMap.ext
    intro w
    change row b (f * w.val.val) = row b (v.val.val * w.val.val)
    rw [← e, add_mul, map_add, coeffEval_pair_suffixLiveContrasts_eq_zero cl a w.val.property,
      zero_add]
  exact RKCert.ReviewedNative.CompensatedRestrictionRank.finrank_debit_of_in_range θ
    inc killed fit

/-- The separate forward and reverse accounts with no saturation condition.
The real local codimension is kept, not replaced by all reverse slack. -/
theorem even_paid_suffix_contrast_ledger
    (ha : A.IsLowerTriangular) (ho : HasOrder p A b) (rpay : q+n+2 ≤ p)
    (qpos : 1 ≤ q) (epay : 2*q ≤ p) (first : firstSeed A b ∈ tailZero u)
    (cl : ∀ i, u ≤ i → b i ≠ 0 → reflectedClock A i = y) :
    let t := finrank K (suffixLiveContrasts b u ⧸ suffixContrastFront A b u q)
    let ρ := finrank K (suffixContrastFrontPairing A b u q).range
    let W := finrank K (treeSpace A q) + finrank K (primitiveBack A b n)
    (finrank K (suffixContrastLowerClockSpan A q) + ρ ≤ finrank K (zeroSpace A q)) ∧
    (finrank K (suffixContrastPairing b u).range ≤ ρ + 2*t) ∧ W+t ≤ s := by
  dsimp only
  refine ⟨even_paid_suffix_front_pairing_debit ho qpos epay cl,
    RKCert.ReviewedNative.PairingRestrictionRank.finrank_pairing_le_restrict_add_twice_codim
      (suffixContrastPairing b u) (suffixContrastFront A b u q), ?_⟩
  let C := suffixLiveContrasts b u
  let T := treeSpace A q
  let V := suffixContrastFront A b u q
  have vdim : finrank K V = finrank K (↥(C ⊓ T : Submodule K (Fin s → K))) := by
    rw [← Submodule.finrank_map_subtype_eq C V, show V = T.comap C.subtype from rfl,
      Submodule.map_comap_subtype]
  have quotientDim := V.finrank_quotient_add_finrank
  rw [vdim] at quotientDim
  change finrank K (C ⧸ V) + finrank K (↥(C ⊓ T : Submodule K (Fin s → K))) = finrank K C at quotientDim
  have slack := suffixLiveContrasts_inter_treeSpace_codim_le_reverse_slack ha ho rpay first cl
  change finrank K C + finrank K T + finrank K (primitiveBack A b n) ≤
    s + finrank K (↥(C ⊓ T : Submodule K (Fin s → K))) at slack
  change finrank K T + finrank K (primitiveBack A b n) + finrank K (C ⧸ V) ≤ s
  omega

/-- Intrinsic midpoint width, keeping the true degree-q polynomial and
defect dimensions rather than assuming explicit polynomial separation. -/
theorem even_paid_suffix_general_rank_width
    (ha : A.IsLowerTriangular) (ho : HasOrder p A b) (rpay : q+n+2 ≤ p)
    (qpos : 1 ≤ q) (epay : 2*q ≤ p) (first : firstSeed A b ∈ tailZero u)
    (cl : ∀ i, u ≤ i → b i ≠ 0 → reflectedClock A i = y)
    {a : ℕ} (rankLower : a ≤ finrank K (suffixContrastPairing b u).range) :
    finrank K (treeSpace A q) + finrank K (primitiveBack A b n) +
      finrank K (suffixContrastLowerClockSpan A q) + (a+1)/2 ≤
        s + finrank K (zeroSpace A q) := by
  obtain ⟨defect, rankDrop, reverse⟩ :=
    even_paid_suffix_contrast_ledger ha ho rpay qpos epay first cl
  let t := finrank K (suffixLiveContrasts b u ⧸ suffixContrastFront A b u q)
  let ρ := finrank K (suffixContrastFrontPairing A b u q).range
  let a0 := finrank K (suffixContrastPairing b u).range
  let d := finrank K (suffixContrastLowerClockSpan A q)
  let f := finrank K (zeroSpace A q)
  let W := finrank K (treeSpace A q) + finrank K (primitiveBack A b n)
  change d+ρ ≤ f at defect
  change a0 ≤ ρ+2*t at rankDrop
  change W+t ≤ s at reverse
  change a ≤ a0 at rankLower
  change W+d+(a+1)/2 ≤ s+f
  omega

/-- The physical contrast charge from exactly the original nonzero
weights, including cancellation only when their signed cut mass is zero. -/
theorem even_paid_live_suffix_contrast_width
    (ha : A.IsLowerTriangular) (ho : HasOrder p A b) (rpay : q+n+2 ≤ p)
    (qpos : 1 ≤ q) (epay : 2*q ≤ p) (first : firstSeed A b ∈ tailZero u)
    (cl : ∀ i, u ≤ i → b i ≠ 0 → reflectedClock A i = y)
    (live : (suffixLiveStages b u).Nonempty) :
    let k := (suffixLiveStages b u).card
    let loss : ℕ := if liveSuffixMass b u = 0 then 1 else 0
    finrank K (treeSpace A q) + finrank K (primitiveBack A b n) +
      finrank K (suffixContrastLowerClockSpan A q) + ((k-1-loss)+1)/2 ≤
        s + finrank K (zeroSpace A q) := by
  classical
  let loss : ℕ := if liveSuffixMass b u = 0 then 1 else 0
  let k := (suffixLiveStages b u).card
  change finrank K (treeSpace A q) + finrank K (primitiveBack A b n) +
    finrank K (suffixContrastLowerClockSpan A q) + ((k-1-loss)+1)/2 ≤
      s + finrank K (zeroSpace A q)
  apply even_paid_suffix_general_rank_width ha ho rpay qpos epay first cl
    (a := k-1-loss)
  have rank := finrank_suffixContrastPairing_range_add_losses (b := b) (u := u) live
  change finrank K (suffixContrastPairing b u).range + loss + 1 = k at rank
  omega

end
end RKResearch.Certified.Graded.Reverse
