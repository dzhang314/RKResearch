module

public import RKCert.ReviewedNative.ClockOnePaidTrace
public import RKCert.ReviewedNative.CompensatedRestrictionRank
public import RKCert.ReviewedNative.UnitBetaSquareMass
import RKCert.ReviewedNative.OrderedNodalGain
import Mathlib.Algebra.Polynomial.Eval.SMul
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Compensated defect rank on actual clock-one coordinates
The stage indices and their tree-space memberships are inputs. The proof
earns the common endpoint kernel by normalizing one actual live coordinate.
It does not assume signed mass noncancellation or a chronological cover. -/
namespace RKResearch.Certified.Graded.Reverse

open RKResearch Polynomial Module
open scoped BigOperators Matrix

noncomputable section

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {s p n : ℕ}
variable {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : Fin (s+1) → K}
variable {ι : Type*} [Fintype ι]

/-- Restriction to specified original coordinates, without moving stages. -/
def clockOneRestriction (σ : ι → Fin (s+1)) : (Fin (s+1) → K) →ₗ[K] (ι → K) :=
  LinearMap.pi (fun i => LinearMap.proj (σ i))

@[simp] theorem clockOneRestriction_apply (σ : ι → Fin (s+1))
    (v : Fin (s+1) → K) (i : ι) :
    clockOneRestriction σ v i = v (σ i) := rfl

/-- The lower defects and their actual one-step clock images. -/
abbrev clockOneLowerSpan (A : Matrix (Fin (s+1)) (Fin (s+1)) K) (n : ℕ) :
    Submodule K (Fin (s+1) → K) :=
  zeroSpace A n ⊔ (zeroSpace A n).map (diag (nodes A))

private theorem unitMass_scale_middle (a : K) (P H : K[X]) :
    clockOneUnitMass (X*(a • P)*H) = a * clockOneUnitMass (X*P*H) := by
  rw [mul_smul_comm, smul_mul_assoc, map_smul, smul_eq_mul]

private theorem unitMass_X_self_pos {P : K[X]} (nz : P ≠ 0) :
    0 < clockOneUnitMass (X*P*P) := by
  simpa only [clockOneUnitMass_apply, formalPrimitive_eq_native, pow_two, mul_assoc] using
    (RKCert.ReviewedNative.UnitBetaSquareMass.X_square_pos nz)

private theorem eq_of_same_unit_X_tests {P Q : K[X]}
    (pd : P.natDegree ≤ n) (qd : Q.natDegree ≤ n)
    (eq : ∀ H : K[X], H.natDegree ≤ n →
      clockOneUnitMass (X*P*H) = clockOneUnitMass (X*Q*H)) :
    P = Q := by
  by_contra ne
  let D := P-Q
  have Dd : D.natDegree ≤ n := by
    simpa only [D, max_self] using natDegree_sub_le_of_le pd qd
  have Dn : D ≠ 0 := by
    intro z
    exact ne (sub_eq_zero.mp z)
  have pr : X*D*D = X*P*D - X*Q*D := by
    change X*(P-Q)*D = _
    rw [mul_sub X P Q, sub_mul]
  have zero : clockOneUnitMass (X*D*D) = 0 := by
    rw [pr, map_sub, eq D Dd, sub_self]
  exact (ne_of_gt (unitMass_X_self_pos Dn)) zero

/-- Paid clock-one indicators force the exact compensated rank debit. The
exceptional balance loses one dimension, not the entire block. -/
theorem clock_one_compensated_rank
    (ha : ∀ i r, i ≤ r → A i r = 0) (ho : HasOrder p A b) (pay : 2*(n+1) ≤ p)
    (σ : ι → Fin (s+1)) (inj : Function.Injective σ) (inh : Nonempty ι)
    (one : ∀ i, nodes A (σ i) = 1) (live : ∀ i, b (σ i) ≠ 0)
    (inE : ∀ i, coordinate (K := K) (σ i) ∈ treeSpace A (n+1)) :
    ∃ R : K[X], R.natDegree ≤ n ∧ 0 < R.eval 1 ∧
      (∀ H : K[X], H.natDegree ≤ n → clockOneUnitMass (X*R*H) = H.eval 1) ∧
      ((R.eval 1 * (∑ i, b (σ i)) ≠ 1) →
        finrank K (clockOneLowerSpan A n) + Fintype.card ι ≤ finrank K (zeroSpace A (n+1))) ∧
      ((R.eval 1 * (∑ i, b (σ i)) = 1) →
        finrank K (clockOneLowerSpan A n) + Fintype.card ι ≤ finrank K (zeroSpace A (n+1)) + 1) := by
  classical
  let a := Classical.choice inh
  obtain ⟨G, g, Gd, gin, gsum, gtests⟩ :=
    clock_one_coordinate_paid_trace ha ho pay (σ a) (one a) (inE a)
  let R := (b (σ a))⁻¹ • G
  have Rd : R.natDegree ≤ n := (natDegree_smul_le _ _).trans Gd
  have kr (H : K[X]) (Hd : H.natDegree ≤ n) :
      clockOneUnitMass (X*R*H) = H.eval 1 := by
    rw [show R = (b (σ a))⁻¹ • G from rfl, unitMass_scale_middle, gtests H Hd,
      ← mul_assoc, inv_mul_cancel₀ (live a), one_mul]
  have Rn : R ≠ 0 := by
    intro rz
    have h := kr (1 : K[X]) (by simp)
    rw [rz, mul_zero, zero_mul, map_zero, eval_one] at h
    exact zero_ne_one h
  have Rp : 0 < R.eval 1 := by
    have pos := unitMass_X_self_pos Rn
    rwa [kr R Rd] at pos
  let W := evalNodes A (X*R)
  have wsite (i : ι) : W (σ i) = R.eval 1 := by
    simp only [W, evalNodes_apply, eval_mul, eval_X, one i, one_mul]
  let error (i : ι) := coordinate (K := K) (σ i) - b (σ i) • W
  have errMem (i : ι) : error i ∈ zeroSpace A (n+1) := by
    obtain ⟨P, f, Pd, fmem, psum, ptests⟩ :=
      clock_one_coordinate_paid_trace ha ho pay (σ i) (one i) (inE i)
    have Peq : P = b (σ i) • R := by
      apply eq_of_same_unit_X_tests Pd ((natDegree_smul_le _ _).trans Rd)
      intro H Hd
      rw [ptests H Hd, unitMass_scale_middle, kr H Hd]
    have ev : evalNodes A (X*P) = b (σ i) • W := by
      rw [Peq, mul_smul_comm, map_smul]
    rw [ev] at psum
    change coordinate (K := K) (σ i) - b (σ i) • W ∈ zeroSpace A (n+1)
    rwa [← psum, add_sub_cancel_left]
  let ρ : (Fin (s+1) → K) →ₗ[K] (ι → K) := clockOneRestriction σ
  let F := zeroSpace A (n+1)
  have fit : LinearMap.range
      (RKCert.ReviewedNative.CompensatedRestrictionRank.coordinateUpdate
        (fun i => b (σ i)) (R.eval 1)) ≤ LinearMap.range (ρ.domRestrict F) := by
    rintro _ ⟨v, rfl⟩
    let u := ∑ i, v i • error i
    have um : u ∈ F := (zeroSpace A (n+1)).sum_mem
      (fun i _ => (zeroSpace A (n+1)).smul_mem (v i) (errMem i))
    refine ⟨⟨u, um⟩, ?_⟩
    ext j
    have eye : (∑ i, v i * coordinate (K := K) (σ i) (σ j)) = v j := by
      rw [Finset.sum_eq_single j]
      · rw [coordinate_same_apply, mul_one]
      · intro i _ ne
        have ne' : σ j ≠ σ i := fun e => ne (inj e).symm
        rw [coordinate_ne_apply ne', mul_zero]
      · intro no
        exact (no (Finset.mem_univ j)).elim
    have mm : (∑ i, v i * (b (σ i) * R.eval 1)) = R.eval 1 * ∑ i, b (σ i) * v i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ac_rfl
    change u (σ j) = RKCert.ReviewedNative.CompensatedRestrictionRank.coordinateUpdate
      (fun i => b (σ i)) (R.eval 1) v j
    rw [RKCert.ReviewedNative.CompensatedRestrictionRank.coordinateUpdate_apply]
    change (∑ i, v i • (coordinate (K := K) (σ i) - b (σ i) • W)) (σ j) = _
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, wsite,
      mul_sub, Finset.sum_sub_distrib, eye, mm]
  have inc : clockOneLowerSpan A n ≤ F :=
    sup_le (zeroSpace_mono A (Nat.le_succ n))
      (Submodule.map_le_iff_le_comap.mpr (diag_zeroSpace A n))
  have lowZero (u : Fin (s+1) → K) (hu : u ∈ zeroSpace A n) (i : ι) :
      u (σ i) = 0 :=
    paid_coordinate_defect_zero (j := n+1) (n := n) ho (by omega)
      (σ i) (inE i) (live i) hu
  have killed : clockOneLowerSpan A n ≤ LinearMap.ker ρ := by
    intro z hz
    obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hz
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hw
    apply LinearMap.mem_ker.mpr
    ext i
    change u (σ i) + diag (nodes A) v (σ i) = 0
    rw [lowZero u hu i, diag_apply, lowZero v hv i, mul_zero, add_zero]
  have debit := RKCert.ReviewedNative.CompensatedRestrictionRank.finrank_debit_of_in_range
    ρ inc killed fit
  refine ⟨R, Rd, Rp, kr, ?_, ?_⟩
  · intro h
    have r := RKCert.ReviewedNative.CompensatedRestrictionRank.coordinate_finrank_of_ne_one
      (fun i => b (σ i)) (R.eval 1) h
    simpa only [r] using debit
  · intro h
    have r := RKCert.ReviewedNative.CompensatedRestrictionRank.coordinate_finrank_add_one_of_eq_one
      (fun i => b (σ i)) (R.eval 1) h
    have z := Nat.add_le_add_right debit 1
    simpa only [Nat.add_assoc, r] using z

end
end RKResearch.Certified.Graded.Reverse
