module
public import RKCert.CauchyKernel
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

@[expose] public section

/-! # Cauchy elimination and the nonzero aggregate node count
No ordering or positivity is used, even for complex knot locations or cancelling weights. -/
namespace RKCert.Endpoint
open scoped Classical
variable {K : Type*} [Field K]

/-- Every square Cauchy slice is injective with exactly the elementary distinctness
and no-pole assumptions.  The proof performs a Schur elimination over the field. -/
theorem cauchy_kernel {n : ℕ} (x y v : Fin n → K)
    (hx : Function.Injective x) (hy : Function.Injective y)
    (hxy : ∀ i j, x i + y j ≠ 0)
    (h : ∀ i, ∑ j : Fin n, v j / (x i + y j) = 0) : v = 0 := by
  exact funext (RKCert.Paired.cauchy_kernel x y v hx hy hxy h)

variable [CharZero K]

/-- The shifted Hilbert moment matrix is injective for all sizes; the shift
is a nonzero natural.  Testing a single variable square would be invalid here. -/
theorem shifted_hilbert_kernel {n : ℕ} (d : ℕ) (hd : 0 < d) (v : Fin n → K)
    (h : ∀ i : Fin n, ∑ j : Fin n, v j / ((i.val+j.val+d : ℕ) : K) = 0) : v = 0 := by
  let x : Fin n → K := fun i => (i.val : K)
  let y : Fin n → K := fun j => ((j.val + d : ℕ) : K)
  have hx : Function.Injective x := by
    intro i j e; exact Fin.ext (Nat.cast_injective (R := K) e)
  have hy : Function.Injective y := by
    intro i j e; have t : i.val+d = j.val+d := Nat.cast_injective (R := K) e
    exact Fin.ext (by omega)
  have val (i j : Fin n) : x i+y j = ((i.val+j.val+d : ℕ) : K) := by
    dsimp [x,y]; push_cast; ring
  apply cauchy_kernel x y v hx hy
  · intro i j; rw [val]; exact Nat.cast_ne_zero.mpr (by omega)
  · simpa only [val] using h

noncomputable def combinedMass {s : ℕ} (c b : Fin s → K) (z : K) : K := by
  classical
  exact ∑ i : Fin s with c i=z, b i

/-- Zero knots and knots with zero NET weight are not counted. -/
noncomputable def activeNonzero {s : ℕ} (c b : Fin s → K) : Finset K := by
  classical
  exact (Finset.univ.image c).filter fun z => z ≠ 0 ∧ combinedMass c b z ≠ 0

omit [CharZero K] in
private theorem group_sum {s : ℕ} (c b : Fin s → K) (f : K → K) :
    ∑ i : Fin s, b i * f (c i) =
       ∑ z ∈ Finset.univ.image c, combinedMass c b z * f z := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (fun i (_ : i ∈ (Finset.univ : Finset (Fin s))) =>
    Finset.mem_image_of_mem c (Finset.mem_univ i)) (fun i => b i*f (c i))]
  apply Finset.sum_congr rfl
  intro z _
  rw [combinedMass, Finset.sum_mul]
  apply Finset.sum_congr (by ext i; simp)
  intro i hi
  rw [(Finset.mem_filter.mp hi).2]

omit [CharZero K] in
private theorem kill_weighted {s : ℕ} (c b : Fin s → K) (f : K → K)
    (h0 : f 0 = 0) (hz : ∀ z ∈ activeNonzero c b, f z = 0) :
    ∑ i : Fin s, b i * f (c i) = 0 := by
  classical
  rw [group_sum]
  apply Finset.sum_eq_zero
  intro z h
  by_cases a : z = 0
  · simp [a,h0]
  by_cases w : combinedMass c b z = 0
  · simp [w]
  rw [hz z (by exact Finset.mem_filter.mpr ⟨h,a,w⟩), mul_zero]

private noncomputable def samples (m : ℕ) (S : Finset K) : (Fin m → K) →ₗ[K] (S → K) where
  toFun v z := ∑ j, v j * (z : K)^j.val
  map_add' u v := by ext z; simp [add_mul, Finset.sum_add_distrib]
  map_smul' a v := by
    ext z; simp [Finset.mul_sum, mul_assoc]

/-- A genuine tableau of tree order p requires at least floor(p/2) distinct
NONZERO abscissae with NONZERO aggregate mass, over every characteristic-zero
field. A can even be fully implicit. -/
theorem activeNonzero_card_of_treeOrder {s p : ℕ} {A : Fin s → Fin s → K}
    {b : Fin s → K} (ho : HasTreeOrderAtLeast A b p) :
    p / 2 ≤ (activeNonzero (nodes A) b).card := by
  classical
  let c := nodes A
  let m := p/2
  let S := activeNonzero c b
  let E := samples m S
  have hm := hasMomentsThrough_of_treeOrder ho
  have mu (k : ℕ) (hk : k+1 ≤ p) : ∑ i : Fin s, b i*c i^k = 1/((k+1:ℕ):K) := by
    apply (eq_div_iff (Nat.cast_ne_zero.mpr (by omega) : ((k+1 : ℕ) : K) ≠ 0)).2
    simpa only [mul_comm] using hm k hk
  have hin : Function.Injective E := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v he
    apply shifted_hilbert_kernel 2 (by decide)
    intro i
    have obs (z : K) (hz : z ∈ S) : ∑ j : Fin m, v j*z^j.val = 0 := congrFun he ⟨z,hz⟩
    have hzero := kill_weighted c b (fun z => z^(i.val+1)*∑ j : Fin m, v j*z^j.val)
      (by simp) (fun z hz => by rw [obs z hz, mul_zero])
    calc
      ∑ j : Fin m, v j / ((i.val+j.val+2 : ℕ) : K) =
          ∑ j : Fin m, v j*(∑ l : Fin s, b l*c l^(i.val+1+j.val)) := by
            apply Finset.sum_congr rfl
            intro j hj
            have hk : i.val+1+j.val+1 ≤ p := by
              have hi := i.isLt; have hJ := j.isLt; dsimp [m] at hi hJ; omega
            rw [mu _ hk]
            have eq : i.val + 1 + j.val + 1 = i.val+j.val+2 := by omega
            rw [eq, div_eq_mul_inv, one_div]
      _ = ∑ l : Fin s, b l * (c l^(i.val+1) * ∑ j : Fin m, v j*c l^j.val) := by
        simp only [Finset.mul_sum, pow_add]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro j _
        ac_rfl
      _ = 0 := hzero
  have hu := LinearMap.finrank_le_finrank_of_injective hin
  simpa only [Module.finrank_pi, Fintype.card_fin, Fintype.card_coe] using hu

end RKCert.Endpoint

