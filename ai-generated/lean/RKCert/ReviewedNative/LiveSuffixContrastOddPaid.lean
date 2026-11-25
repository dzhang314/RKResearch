module

public import RKCert.ReviewedNative.ConstantLiveSuffixContrasts
public import RKCert.ReviewedNative.GradedProducts
public import RKCert.ReviewedNative.GradedSeparation
public import RKCert.ReviewedNative.PairingRestrictionRank
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Odd-paid native contrasts on a single live suffix clock

One further original order condition moves the Gram charge out of the
forward defect jump and into reverse slack. The polynomial Cauchy test
and the rooted-tree product both retain the original tableau. -/
namespace RKResearch.Certified.Graded.Reverse

open RKResearch Module
open scoped Matrix

noncomputable section

variable {K : Type*} [Field K] {s p q n : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
variable {u : Fin s} {y : K}

/-- Every ordinary probe equals a scalar times signed mass on the original
live-clock support. No order payment is needed for this algebraic step. -/
theorem probe_suffixLiveContrasts_eq_zero
    (cl : ∀ i, u ≤ i → b i ≠ 0 → reflectedClock A i = y)
    {v : Fin s → K} (hv : v ∈ suffixLiveContrasts b u) (k : ℕ) :
    probe A b k v = 0 := by
  obtain ⟨off, mass⟩ := mem_suffixLiveContrasts.mp hv
  have same : probe A b k v = (1 - y) ^ k * row b v := by
    simp only [probe, row_apply, dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i ∈ suffixLiveStages b u
    · obtain ⟨ui, bi⟩ := mem_suffixLiveStages.mp hi
      have h := cl i ui bi
      change (1 : K) - nodes A i = y at h
      have x : nodes A i = 1 - y := by rw [← h, sub_sub_cancel]
      rw [x]
      ac_rfl
    · have hv0 := off i hi
      simp only [hv0, mul_zero]
  rw [same, mass, mul_zero]

/-- Every signed contrast in the genuine tree space is already a
homogeneous defect once all q+1 ordinary Cauchy tests are paid. -/
theorem suffixLiveContrasts_inter_treeSpace_le_zeroSpace (ho : HasOrder p A b)
    (pay : 2*q+1 ≤ p)
    (cl : ∀ i, u ≤ i → b i ≠ 0 → reflectedClock A i = y) :
    suffixLiveContrasts b u ⊓ treeSpace A q ≤ zeroSpace A q := by
  intro v hv
  obtain ⟨hc, ht⟩ := Submodule.mem_inf.mp hv
  rw [treeSpace_coeff_sup ho (by omega : q+1 ≤ p)] at ht
  obtain ⟨v', hv', f, hf, e⟩ := Submodule.mem_sup.mp ht
  obtain ⟨a, rfl⟩ := hv'
  have test (i : Fin (q+1)) :
      (∑ j : Fin (q+1), a j / ((i.val+j.val+1 : ℕ) : K)) = 0 := by
    have ip := i.isLt
    have ep := probe_suffixLiveContrasts_eq_zero cl hc i.val
    have f0 : probe A b i.val f = 0 := probe_zeroSpace (k := i.val) ho (by omega) hf
    rw [← e, map_add, f0, add_zero, probe_coeffEval ho (by omega)] at ep
    exact ep
  have coef : ∀ j, a j = 0 := moments_detect ho (d := 1) (by decide) (by omega)
    (fun i j => by have := i.isLt; have := j.isLt; omega) a test
  have z : a = 0 := funext coef
  rw [z, map_zero, zero_add] at e
  exact e ▸ hf

/-- The genuine forward intersection of the live contrast space is
totally isotropic for the original signed-output pairing. -/
theorem suffixLiveContrasts_inter_treeSpace_pair_zero (ho : HasOrder p A b)
    (pay : 2*q+1 ≤ p)
    (cl : ∀ i, u ≤ i → b i ≠ 0 → reflectedClock A i = y)
    {v w : Fin s → K}
    (hv : v ∈ suffixLiveContrasts b u ⊓ treeSpace A q)
    (hw : w ∈ suffixLiveContrasts b u ⊓ treeSpace A q) :
    row b (v * w) = 0 := by
  have vf := suffixLiveContrasts_inter_treeSpace_le_zeroSpace ho pay cl hv
  have wt := (Submodule.mem_inf.mp hw).2
  have prod : v * w ∈ zeroSpace A (q+q) :=
    zeroSpace_mul_treeSpace ho (by omega : q+1 ≤ p) vf wt
  have z : probe A b 0 (v * w) = 0 := probe_zeroSpace (k := 0) ho (by omega) prod
  simpa only [probe, pow_zero, mul_one] using z

/-- Bilinear signed output, acting on the ambient original stage vectors. -/
def suffixSignedPairing (b : Fin s → K) :
    (Fin s → K) →ₗ[K] Dual K (Fin s → K) :=
  (LinearMap.compRight K (row b)).comp (LinearMap.mul K (Fin s → K))

@[simp] theorem suffixSignedPairing_apply (b v w : Fin s → K) :
    suffixSignedPairing b v w = row b (v * w) := rfl

/-- Its restriction to the supported contrast carrier. -/
abbrev suffixContrastPairing (b : Fin s → K) (u : Fin s) :
    suffixLiveContrasts b u →ₗ[K] Dual K (suffixLiveContrasts b u) :=
  (suffixLiveContrasts b u).dualRestrict.comp
    ((suffixSignedPairing b).domRestrict (suffixLiveContrasts b u))

@[simp] theorem suffixContrastPairing_apply (b : Fin s → K) (u : Fin s)
    (v w : suffixLiveContrasts b u) :
    suffixContrastPairing b u v w = row b (v.val * w.val) := rfl

/-- At odd payment, the entire measured rank of the original contrast
pairing is at most twice the measured reverse slack. A numerical rank
formula on live coordinates can be supplied independently. -/
theorem suffix_contrast_pairing_rank_le_twice_reverse_slack
    (ha : A.IsLowerTriangular) (ho : HasOrder p A b) (rpay : q+n+2 ≤ p)
    (opay : 2*q+1 ≤ p) (first : firstSeed A b ∈ tailZero u)
    (cl : ∀ i, u ≤ i → b i ≠ 0 → reflectedClock A i = y) :
    finrank K (suffixContrastPairing b u).range +
        2 * (finrank K (treeSpace A q) + finrank K (primitiveBack A b n)) ≤ 2*s := by
  let C := suffixLiveContrasts b u
  let T := treeSpace A q
  let V := T.comap C.subtype
  have zero : V.dualRestrict.comp ((suffixContrastPairing b u).domRestrict V) = 0 := by
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro w
    change row b (v.val.val * w.val.val) = 0
    have hv : v.val.val ∈ C ⊓ T := Submodule.mem_inf.mpr ⟨v.val.property, v.property⟩
    have hw : w.val.val ∈ C ⊓ T := Submodule.mem_inf.mpr ⟨w.val.property, w.property⟩
    exact suffixLiveContrasts_inter_treeSpace_pair_zero ho opay cl hv hw
  have rankDrop :=
    RKCert.ReviewedNative.PairingRestrictionRank.finrank_pairing_le_restrict_add_twice_codim
      (suffixContrastPairing b u) V
  rw [zero, LinearMap.range_zero, finrank_bot, zero_add] at rankDrop
  have vdim : finrank K V = finrank K (↥(C ⊓ T : Submodule K (Fin s → K))) := by
    rw [← Submodule.finrank_map_subtype_eq C V, show V = T.comap C.subtype from rfl,
      Submodule.map_comap_subtype]
  have quotientDim := V.finrank_quotient_add_finrank
  rw [vdim] at quotientDim
  have slack := suffixLiveContrasts_inter_treeSpace_codim_le_reverse_slack ha ho rpay first cl
  change finrank K C + finrank K T + finrank K (primitiveBack A b n) ≤
    s + finrank K (↥(C ⊓ T : Submodule K (Fin s → K))) at slack
  change finrank K (suffixContrastPairing b u).range ≤ 2 * finrank K (C ⧸ V) at rankDrop
  change finrank K (suffixContrastPairing b u).range +
    2 * (finrank K T + finrank K (primitiveBack A b n)) ≤ 2*s
  omega

/-- Numeric wrapper with a separately certified lower rank. In particular,
the live-coordinate rank k−1−δ gives its ceiling-half as reverse slack. -/
theorem suffix_contrast_rank_floor_add_reverse_le_stages
    (ha : A.IsLowerTriangular) (ho : HasOrder p A b) (rpay : q+n+2 ≤ p)
    (opay : 2*q+1 ≤ p) (first : firstSeed A b ∈ tailZero u)
    (cl : ∀ i, u ≤ i → b i ≠ 0 → reflectedClock A i = y)
    {a : ℕ} (rankLower : a ≤ finrank K (suffixContrastPairing b u).range) :
    finrank K (treeSpace A q) + finrank K (primitiveBack A b n) + (a+1)/2 ≤ s := by
  have h := suffix_contrast_pairing_rank_le_twice_reverse_slack ha ho rpay opay first cl
  omega

end
end RKResearch.Certified.Graded.Reverse
