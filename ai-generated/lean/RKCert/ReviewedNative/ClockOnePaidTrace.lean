module

public import RKCert.ReviewedNative.GradedProducts
public import RKCert.ReviewedNative.PolynomialStageSeparation
public import RKCert.ReviewedNative.RowAnnihilator
public import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.Polynomial.Div
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Paid native moment of an original clock-one coordinate
No chronological or reverse-capacity premise is assumed here. The consumer
must already place the literal coordinate in the actual native tree space. -/
namespace RKResearch.Certified.Graded.Reverse

open RKResearch Polynomial Module
open scoped BigOperators Matrix

noncomputable section

variable {K : Type*} [Field K]
variable {s p n j : ℕ}
variable {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : Fin (s+1) → K}

/-- Unit primitive mass in the native normalization. -/
abbrev clockOneUnitMass : K[X] →ₗ[K] K :=
  (Polynomial.leval 1).comp primitive

@[simp] theorem clockOneUnitMass_apply (P : K[X]) :
    clockOneUnitMass P = (primitive P).eval 1 := rfl

theorem coordinate_same_apply (i : Fin (s+1)) :
    coordinate (K := K) i i = 1 := by
  classical
  simp [coordinate]

theorem coordinate_ne_apply {i r : Fin (s+1)} (e : r ≠ i) :
    coordinate (K := K) i r = 0 := by
  classical
  simp [coordinate, e]

private theorem native_mul_coordinate (v : Fin (s+1) → K) (i : Fin (s+1)) :
    v * coordinate (K := K) i = v i • coordinate i := by
  ext r
  by_cases e : r = i
  · subst r
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul, coordinate_same_apply]
  · simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul, coordinate_ne_apply e, mul_zero]

private theorem probe_zero_coordinate (i : Fin (s+1)) :
    probe A b 0 (coordinate (K := K) i) = b i := by
  simp only [probe, pow_zero, mul_one, row_coordinate]

/-- A live coordinate of a tree space is blind to every lower defect
whose tree-product pairing is actually paid. -/
theorem paid_coordinate_defect_zero (ho : HasOrder p A b) (pay : j+n+1 ≤ p)
    (i : Fin (s+1)) (hi : coordinate (K := K) i ∈ treeSpace A j) (bi : b i ≠ 0)
    {v : Fin (s+1) → K} (hv : v ∈ zeroSpace A n) :
    v i = 0 := by
  have z : v * coordinate (K := K) i ∈ zeroSpace A (n+j) :=
    zeroSpace_mul_treeSpace ho (by omega) hv hi
  have e : probe A b 0 (v * coordinate (K := K) i) = 0 :=
    probe_zeroSpace (k := 0) ho (by omega) z
  rw [native_mul_coordinate, map_smul, smul_eq_mul, probe_zero_coordinate] at e
  exact (mul_eq_zero.mp e).resolve_right bi

private theorem probe_coordinate_polynomial (i : Fin (s+1)) (H : K[X]) :
    probe A b 0 (coordinate (K := K) i * evalNodes A H) =
      b i * H.eval (nodes A i) := by
  rw [mul_comm (coordinate (K := K) i) (evalNodes A H), native_mul_coordinate,
    map_smul, smul_eq_mul, probe_zero_coordinate, evalNodes_apply]
  exact mul_comm _ _

private theorem strict_origin_node
    (ha : ∀ i r, i ≤ r → A i r = 0) :
    nodes A 0 = 0 := by
  simp only [nodes, Matrix.mulVec, dotProduct]
  exact Finset.sum_eq_zero (fun i _ => by rw [ha 0 i (Fin.zero_le _), zero_mul])

/-- Decompose a paid physical clock-one coordinate and collect exactly the
degree-at-most-n unit tests. These are tests on the original, signed output. -/
theorem clock_one_coordinate_paid_trace
    (ha : ∀ i r, i ≤ r → A i r = 0) (ho : HasOrder p A b)
    (pay : 2*(n+1) ≤ p) (i : Fin (s+1))
    (one : nodes A i = 1)
    (inE : coordinate (K := K) i ∈ treeSpace A (n+1)) :
    ∃ (R : K[X]) (f : Fin (s+1) → K),
      R.natDegree ≤ n ∧ f ∈ zeroSpace A (n+1) ∧
      evalNodes A (X*R) + f = coordinate (K := K) i ∧
      ∀ H : K[X], H.natDegree ≤ n → clockOneUnitMass (X*R*H) = b i * H.eval 1 := by
  classical
  have o : (0 : Fin (s+1)) ≠ i := by
    intro h
    have e := congrArg (fun r => nodes A r) h
    rw [strict_origin_node ha, one] at e
    exact zero_ne_one e
  rw [treeSpace_coeff_sup ho (by omega : n+2 ≤ p)] at inE
  obtain ⟨v, hv, f, hf, eq⟩ := Submodule.mem_sup.mp inE
  obtain ⟨a, rfl⟩ := hv
  let P : K[X] := ofFn (n+1+1) a
  have Pd : P.natDegree ≤ n+1 := by
    exact Nat.le_of_lt_succ (ofFn_natDegree_lt (by omega : 1 ≤ n+1+1) a)
  have ev : evalNodes A P = coeffEval A (n+1) a := by
    rw [evalNodes_eq_coeffEval A P Pd]
    congr 1
    exact toFn_comp_ofFn_eq_id _ _
  have P0 : P.coeff 0 = 0 := by
    rw [coeff_zero_eq_eval_zero]
    have f0 : f 0 = 0 := origin_zeroSpace ha (n+1) hf
    have e := congrFun eq (0 : Fin (s+1))
    rw [Pi.add_apply, ← ev, evalNodes_apply, strict_origin_node ha,
      f0, add_zero, coordinate_ne_apply o] at e
    exact e
  obtain ⟨R, hR⟩ := X_dvd_iff.mpr P0
  have Rd : R.natDegree ≤ n := by
    by_cases rz : R = 0
    · simp [rz]
    · rw [hR, natDegree_X_mul rz] at Pd
      omega
  have eq' : evalNodes A (X*R) + f = coordinate (K := K) i := by
    rw [← hR, ev, eq]
  refine ⟨R, f, Rd, hf, eq',?_⟩
  intro H Hd
  have XRd : (X*R).natDegree ≤ n+1 := by
    have d := natDegree_mul_le_of_le (show (X : K[X]).natDegree ≤ 1 from natDegree_X.le) Rd
    omega
  have prodD := natDegree_mul_le_of_le XRd Hd
  have z : f * evalNodes A H ∈ zeroSpace A (n+1+n) :=
    zeroSpace_mul_treeSpace ho (by omega) hf (evalNodes_mem_treeSpace A H Hd)
  have f0 : probe A b 0 (f * evalNodes A H) = 0 :=
    probe_zeroSpace (k := 0) ho (by omega) z
  have m := probe_evalNodes ho (X*R*H) 0 (by omega)
  have vmul : evalNodes A (X*R*H) = evalNodes A (X*R) * evalNodes A H := by
    ext r
    simp only [evalNodes_apply, eval_mul, Pi.mul_apply]
  have e : coordinate (K := K) i * evalNodes A H =
      evalNodes A (X*R*H) + f * evalNodes A H := by
    rw [← eq', add_mul, vmul]
  calc
    clockOneUnitMass (X*R*H) = probe A b 0 (evalNodes A (X*R*H)) := by
      simpa only [clockOneUnitMass_apply, pow_zero, one_mul] using m.symm
    _ = probe A b 0 (coordinate (K := K) i * evalNodes A H) := by
      rw [e, map_add, f0, add_zero]
    _ = b i * H.eval 1 := by rw [probe_coordinate_polynomial, one]

end
end RKResearch.Certified.Graded.Reverse
