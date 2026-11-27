module

public import RKCert.ReviewedNative.GradedDefects
public import RKCert.ReviewedNative.RationalPrimeNodalSupport
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases

@[expose] public section

/-! # The paid adjoint and fibre kernel of a nine-stage collision

These tools use the actual reviewed rooted order conditions. The main
right rows do not assume simplifying adjoint conditions pointwise:
their equality is first established only after grouping equal clocks. -/

namespace RKResearch.Certified.SDIRKSevenTailCollision
open RKResearch FiniteRootedTree Graded
open scoped Matrix BigOperators FiniteRootedTree Classical
noncomputable section

variable {ι K : Type*} [Fintype ι] [Field K] [CharZero K]

abbrev x (A : Matrix ι ι K) : ι → K := nodes A
abbrev firstRow (A : Matrix ι ι K) (b : ι → K) := b ᵥ* A
abbrev secondRow (A : Matrix ι ι K) (b : ι → K) := (b * x A) ᵥ* A
abbrev firstTarget (A : Matrix ι ι K) (b : ι → K) := fun i => b i * (1 - x A i)
abbrev secondTarget (A : Matrix ι ι K) (b : ι → K) := fun i => b i * ((1 - (x A i)^2) / 2)
abbrev firstError (A : Matrix ι ι K) (b : ι → K) := firstRow A b - firstTarget A b
abbrev secondError (A : Matrix ι ι K) (b : ι → K) := secondRow A b - secondTarget A b

theorem clock_moment {A : Matrix ι ι K} {b : ι → K} (ho : HasOrder 7 A b)
    (j : ℕ) (hj : j+1 ≤ 7) :
    (∑ i,b i * (x A i)^j) = 1 / ((j:K)+1) := by
  have h := ho.hasQuadratureOrder j hj
  have hd : (j:K)+1 ≠ 0 := by exact_mod_cast j.succ_ne_zero
  apply (eq_div_iff hd).mpr
  simpa only [dotProduct, Pi.pow_apply, mul_comm, Nat.cast_succ] using h

theorem primitive_moment {A : Matrix ι ι K} {b : ι → K} (ho : HasOrder 7 A b)
    (j k : ℕ) (hj : j+k+2 ≤ 7) :
    (∑ i, ((fun l => b l * (x A l)^k) ᵥ* A) i * (x A i)^j) =
      1 / (((j:K)+1) * ((j:K)+(k:K)+2)) := by
  have h := probe_normTree ho (.leaf ◂ clockTree j) k (by
    simp only [order, order_clockTree, PNat.add_coe, PNat.one_coe]; omega)
  rw [normTree_unary, normTree_clockTree, order_clockTree, map_smul, smul_eq_mul] at h
  change ((k + ((.leaf ◂ clockTree j).order : ℕ) : ℕ) : K) *
    (((j+1:ℕ) : K) * ((fun l => b l * (x A l)^k) ⬝ᵥ (A *ᵥ fun i => (x A i)^j))) = 1 at h
  rw [Matrix.dotProduct_mulVec] at h
  simp only [dotProduct, order, order_clockTree, PNat.add_coe, PNat.one_coe,
    Nat.cast_add, Nat.cast_one] at h
  have h1 : (j:K)+1 ≠ 0 := by exact_mod_cast j.succ_ne_zero
  have h2 : (j:K)+(k:K)+2 ≠ 0 := by
    have nonzero : ((j+k+2 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    simpa only [Nat.cast_add, Nat.cast_ofNat] using nonzero
  apply (eq_div_iff (mul_ne_zero h1 h2)).mpr
  linear_combination (norm := ring) h

theorem firstError_moments {A : Matrix ι ι K} {b : ι → K} (ho : HasOrder 7 A b)
    (j : ℕ) (hj : j ≤ 5) : (∑ i,firstError A b i * (x A i)^j) = 0 := by
  have h := primitive_moment ho j 0 (by omega)
  have q0 := clock_moment ho j (by omega)
  have q1 := clock_moment ho (j+1) (by omega)
  have hb : (fun l => b l * (x A l)^0) = b := by funext l; simp
  rw [hb, Nat.cast_zero, add_zero] at h
  change (∑ i, ((b ᵥ* A) i - b i * (1-x A i))*(x A i)^j) = 0
  simp only [mul_sub, mul_one, sub_mul, Finset.sum_sub_distrib]
  simp only [pow_succ, Nat.cast_add, Nat.cast_one] at q1
  have hA : (∑ i,b i * x A i * (x A i)^j) = ∑ i,b i * ((x A i)^j * x A i) := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hA, h, q0, q1]
  have hn : (j:K)+1 ≠ 0 := by exact_mod_cast j.succ_ne_zero
  have hm : (j:K)+2 ≠ 0 := by
    exact_mod_cast (show j+2 ≠ 0 by omega)
  rw [show (j:K)+1+1=(j:K)+2 by ring]
  field_simp
  ring

theorem secondError_moments {A : Matrix ι ι K} {b : ι → K} (ho : HasOrder 7 A b)
    (j : ℕ) (hj : j ≤ 4) : (∑ i,secondError A b i * (x A i)^j) = 0 := by
  have h := primitive_moment ho j 1 (by omega)
  have q0 := clock_moment ho j (by omega)
  have q2 := clock_moment ho (j+2) (by omega)
  have hb : (fun l => b l * (x A l)^1) = b * x A := by funext l; simp
  rw [hb, Nat.cast_one] at h
  change (∑ i, (((b*x A) ᵥ* A) i - b i * ((1-(x A i)^2)/2))*(x A i)^j) = 0
  simp only [sub_mul, Finset.sum_sub_distrib]
  have hExpr :
      (∑ i,b i * ((1-(x A i)^2)/2) * (x A i)^j) =
      ((∑ i,b i * (x A i)^j) - ∑ i,b i * (x A i)^(j+2))/2 := by
    rw [div_eq_mul_inv, sub_mul, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [pow_add]
    ring
  rw [hExpr, h, q0, q2]
  simp only [Nat.cast_add, Nat.cast_ofNat]
  have hn : (j:K)+1 ≠ 0 := by exact_mod_cast j.succ_ne_zero
  have hm : (j:K)+3 ≠ 0 := by exact_mod_cast (show j+3 ≠ 0 by omega)
  rw [show (j:K)+1+2=(j:K)+3 by ring, show (j:K)+2+1=(j:K)+3 by ring]
  field_simp
  ring

theorem firstError_annihilates {A : Matrix ι ι K} {b : ι → K} (ho : HasOrder 7 A b)
    {v : ι → K} (hv : v ∈ zeroSpace A 5) : (firstError A b ⬝ᵥ v) = 0 := by
  have h0 := LinearMap.mem_ker.mp (probe_zeroSpace ho (k := 0) (by decide) hv)
  have h1 := LinearMap.mem_ker.mp (probe_zeroSpace ho (k := 1) (by decide) hv)
  have hAv := mat_zeroSpace_charZero A 5 hv
  have hA := LinearMap.mem_ker.mp (probe_zeroSpace ho (k := 0) (by decide) hAv)
  have ht : firstTarget A b = b-b*x A := by
    funext i
    change b i * (1-x A i)=b i-b i*x A i
    ring
  rw [show firstError A b = (b ᵥ* A)-(firstTarget A b) from rfl,
    sub_dotProduct, ht, sub_dotProduct, ←Matrix.dotProduct_mulVec]
  simp only [row_apply, pow_zero, mul_one] at h0 hA
  simp only [row_apply, pow_one] at h1
  change ((b * x A) ⬝ᵥ v) = 0 at h1
  change (b ⬝ᵥ (A *ᵥ v)) = 0 at hA
  rw [h0,h1,hA,sub_self,sub_self]

omit [CharZero K] in
/-- Multiplying by distinct linear factors uses exactly their number of
moments. This avoids any choice of a Vandermonde inverse. -/
theorem weighted_product_zero {w c : ι → K} {n : ℕ}
    (hm : ∀ j ≤ n, (∑ i,w i*(c i)^j)=0)
    (s : Finset K) (j : ℕ) (h : j+s.card≤n) :
    (∑ i,w i*(c i)^j*(∏ z ∈ s, (c i-z)))=0 := by
  classical
  induction s using Finset.induction_on generalizing j with
  | empty =>
      simpa using hm j (by simpa using h)
  | @insert z s hz ih =>
      have h1 : j+1+s.card≤n := by rw [Finset.card_insert_of_notMem hz] at h; omega
      have h0 : j+s.card≤n := by omega
      simp only [Finset.prod_insert hz]
      have step :
          (∑ i,w i*(c i)^j*((c i-z)*(∏ t ∈ s,(c i-t)))) =
            (∑ i,w i*(c i)^(j+1)*(∏ t ∈ s,(c i-t))) -
              z*(∑ i,w i*(c i)^j*(∏ t ∈ s,(c i-t))) := by
        rw [Finset.mul_sum, ←Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        rw [pow_succ]
        ring
      rw [step, ih _ h1, ih _ h0, mul_zero, sub_zero]

omit [CharZero K] in
/-- A moment-dead row is zero on each clock fibre, provided the number
of possible contributing clock values is at most one more than the budget. -/
theorem fiber_zero {w c : ι → K} {n : ℕ}
    (hm : ∀ j ≤ n, (∑ i,w i*(c i)^j)=0)
    (s : Finset K) (hsize : s.card ≤ n+1)
    (hs : ∀ i, w i ≠ 0 → c i ∈ s) (a : K) :
    (∑ i ∈ Finset.univ.filter (fun i => c i=a), w i)=0 := by
  classical
  by_cases ha : a ∈ s
  · let val := ∏ z ∈ s.erase a, (a-z)
    have nv : val ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro z hz
      exact sub_ne_zero.mpr (Finset.ne_of_mem_erase hz).symm
    have nz := weighted_product_zero hm (s.erase a) 0 (by rw [Finset.card_erase_of_mem ha]; omega)
    have eq :
        (∑ i,w i*(c i)^0*(∏ z ∈ s.erase a,(c i-z))) =
          (∑ i ∈ Finset.univ.filter (fun i => c i=a),w i)*val := by
      rw [Finset.sum_mul,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : c i=a
      · simp [hi,val]
      · simp only [hi,ite_false,pow_zero,mul_one]
        by_cases hw : w i=0
        · rw [hw,zero_mul]
        · have hh : c i ∈ s.erase a := Finset.mem_erase.mpr ⟨hi,hs i hw⟩
          rw [Finset.prod_eq_zero hh (sub_self _), mul_zero]
    rw [eq] at nz
    exact (mul_eq_zero.mp nz).resolve_right nv
  · apply Finset.sum_eq_zero
    intro i hi
    apply not_ne_iff.mp
    intro hw
    apply ha
    exact (Finset.mem_filter.mp hi).2 ▸ hs i hw

end
end RKResearch.Certified.SDIRKSevenTailCollision
