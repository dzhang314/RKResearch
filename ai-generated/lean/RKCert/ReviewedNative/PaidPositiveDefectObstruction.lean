module

public import RKCert.ReviewedNative.GradedProducts
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Basic
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! Genuine paid squares and nonnegative effective donor links.
No stage ordering, distinct clocks, or diagonal assumption is used. -/

namespace RKResearch.Certified.Graded

open RKResearch
open scoped BigOperators Matrix

section

variable {ι K : Type*} [Fintype ι] [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A : Matrix ι ι K} {b : ι → K} {p g : ℕ}

private theorem paidSquareMass_zero {j : ℕ} {v : ι → K}
    (ho : HasOrder p A b) (pay : j + 1 ≤ p) (hv : v ∈ zeroSpace A j) :
    (∑ i, b i * v i) = 0 := by
  have hker : v ∈ (probe A b 0).ker :=
    probe_zeroSpace (j := j) (k := 0) ho (by simpa only [zero_add] using pay) hv
  have hprobe : probe A b 0 v = 0 := LinearMap.mem_ker.mp hker
  simpa only [probe, row_apply, dotProduct, pow_zero, mul_one] using hprobe

private theorem nonnegMass_terms_zero {f : ι → K}
    (hn : ∀ i, 0 ≤ f i) (hz : (∑ i, f i) = 0) (i : ι) : f i = 0 :=
  (Finset.sum_eq_zero_iff_of_nonneg (f := f) (s := Finset.univ)
    (fun j _ => hn j)).mp hz i (Finset.mem_univ i)

private theorem weightedFactor_zero_of_square_zero {w x : K}
    (h : w * (x * x) = 0) : w * x = 0 := by
  have h' : (w * x) * x = 0 := by
    simpa only [mul_assoc] using h
  rcases mul_eq_zero.mp h' with hz | hz
  · exact hz
  · rw [hz, mul_zero]

/-- A paid defect square kills the weighted defect at every physical stage. -/
theorem paid_defect_weighted_zero_of_nonneg
    (ho : HasOrder p A b) (pay : g + g + 1 ≤ p)
    (hb : ∀ i, 0 ≤ b i) {v : ι → K} (hv : v ∈ zeroSpace A g) :
    ∀ i, b i * v i = 0 := by
  have hsq : v * v ∈ zeroSpace A (g + g) := zeroSpace_mul hv hv
  let f : ι → K := fun i => b i * (v i * v i)
  have hz : (∑ i, f i) = 0 := by
    simpa only [f, Pi.mul_apply] using paidSquareMass_zero ho pay hsq
  have hn (i : ι) : 0 ≤ f i := mul_nonneg (hb i) (mul_self_nonneg (v i))
  intro i
  exact weightedFactor_zero_of_square_zero (nonnegMass_terms_zero hn hz i)

/-- Nonnegative effective links make the earlier paid A(q²) kill each
    link contribution of q and the literal weighted outgoing column. -/
theorem paid_donor_links_and_outgoing_zero
    (ho : HasOrder p A b) (pay : g + g + 2 ≤ p)
    (links : ∀ i j, 0 ≤ b i * A i j)
    {q : ι → K} (hq : q ∈ zeroSpace A g) :
    (∀ i j, (b i * A i j) * q j = 0) ∧
      (∀ i, b i * mat A q i = 0) := by
  have hsq : q * q ∈ zeroSpace A (g + g) := zeroSpace_mul hq hq
  have adv : mat A (q * q) ∈ zeroSpace A (g + g + 1) :=
    mat_zeroSpace ho (g + g) (by omega) hsq
  let f : ι → ι → K := fun i j => (b i * A i j) * (q j * q j)
  have hz : (∑ i, ∑ j, f i j) = 0 := by
    simpa only [f, mat_apply, Matrix.mulVec_apply_eq_sum, Pi.mul_apply, Finset.mul_sum,
      mul_assoc] using paidSquareMass_zero ho (by omega : (g + g + 1) + 1 ≤ p) adv
  have hn (i j : ι) : 0 ≤ f i j := mul_nonneg (links i j) (mul_self_nonneg (q j))
  have rows (i : ι) : (∑ j, f i j) = 0 :=
    nonnegMass_terms_zero (fun u => Finset.sum_nonneg (fun j _ => hn u j)) hz i
  have each (i j : ι) : (b i * A i j) * q j = 0 :=
    weightedFactor_zero_of_square_zero (nonnegMass_terms_zero (hn i) (rows i) j)
  refine ⟨each, ?_⟩
  intro i
  calc
    b i * mat A q i = ∑ j, (b i * A i j) * q j := by
      simp only [mat_apply, Matrix.mulVec_apply_eq_sum, Finset.mul_sum, mul_assoc]
    _ = 0 := Finset.sum_eq_zero (fun j _ => each i j)

/-- Without a sign assumption on the donor links, pay the outgoing square
    one order later. -/
theorem paid_outgoing_weighted_zero_of_nonneg
    (ho : HasOrder p A b) (pay : g + g + 3 ≤ p)
    (hb : ∀ i, 0 ≤ b i) {q : ι → K} (hq : q ∈ zeroSpace A g) :
    ∀ i, b i * mat A q i = 0 := by
  have adv : mat A q ∈ zeroSpace A (g + 1) := mat_zeroSpace ho g (by omega) hq
  exact paid_defect_weighted_zero_of_nonneg ho (by omega) hb adv

end

end RKResearch.Certified.Graded
