module

public import RKCert.ReviewedNative.GradedPrimitives
public import RKCert.ReviewedNative.FiniteCauchy
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Jacobi-free simple roots from two origin values and ordinary moments

The kernel is one-dimensional by a shifted Cauchy system. A polynomial
differential operator preserves the kernel; the ordinary root multiplicity
at a regular point then rules out a common root with the derivative.
No tableaux, order assumptions, or orthogonal polynomial families occur.
-/

namespace RKResearch.Certified.Graded.OriginMomentDifferential

open Polynomial
open scoped BigOperators

variable {K : Type*} [Field K]

/-- The purely algebraic unit-interval moment, sending X^k to 1/(k+1). -/
noncomputable def integral01 : K[X] →ₗ[K] K :=
  (Polynomial.leval (1 : K)).comp primitive

theorem integral01_apply (P : K[X]) :
    integral01 P = (primitive P).eval 1 := rfl

private theorem integral01_monomial (k : ℕ) (s : K) :
    integral01 (monomial k s) = s / ((k+1 : ℕ) : K) := by
  rw [integral01_apply, primitive_monomial, eval_monomial, one_pow, mul_one]

private theorem integral01_power_mul_coeff {P : K[X]} {n : ℕ}
    (d : P.natDegree < n) (k : ℕ) :
    integral01 (X^k * P) =
      ∑ j : Fin n, P.coeff j.val / ((j.val+k+1 : ℕ) : K) := by
  calc
    _ = integral01 (X^k * (∑ j ∈ Finset.range n, monomial j (P.coeff j))) :=
      congrArg (fun S : K[X] => integral01 (X^k * S)) (P.as_sum_range' n d)
    _ = _ := by
      rw [Finset.mul_sum, map_sum, ← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro j _
      rw [X_pow_mul_monomial, integral01_monomial]

/-- Replace the monomial tests by all polynomials of the same degree cap. -/
theorem test_polynomial_of_power {P : K[X]} {n : ℕ}
    (test : ∀ k < n, integral01 (X^k * P) = 0)
    (T : K[X]) (d : T.natDegree < n) :
    integral01 (T * P) = 0 := by
  have e := congrArg (fun S : K[X] => integral01 (S * P))
    (T.as_sum_range_C_mul_X_pow' d)
  rw [Finset.sum_mul, map_sum] at e
  rw [e]
  apply Finset.sum_eq_zero
  intro k hk
  rw [mul_assoc, ← Polynomial.smul_eq_C_mul, map_smul,
    test k (Finset.mem_range.mp hk), smul_zero]

structure Window (n : ℕ) (P : K[X]) : Prop where
  degree : P.natDegree ≤ n+2
  origin : P.eval 0 = 0
  origin_derivative : P.derivative.eval 0 = 0
  moments : ∀ T : K[X], T.natDegree < n → integral01 (T * P) = 0

/-- The inputs can be supplied as n ordinary power moments. -/
theorem Window.of_power {n : ℕ} {P : K[X]} (d : P.natDegree ≤ n+2)
    (h0 : P.eval 0 = 0) (h1 : P.derivative.eval 0 = 0)
    (test : ∀ k < n, integral01 (X^k * P) = 0) : Window n P :=
  ⟨d, h0, h1, test_polynomial_of_power test⟩

private theorem Window.sub {n : ℕ} {P Q : K[X]} (H : Window n P) (G : Window n Q) :
    Window n (P-Q) := by
  refine ⟨(natDegree_sub_le _ _).trans (max_le H.degree G.degree), ?_, ?_, ?_⟩
  · simp only [eval_sub, H.origin, G.origin, sub_zero]
  · simp only [derivative_sub, eval_sub, H.origin_derivative, G.origin_derivative, sub_zero]
  · intro T d
    rw [mul_sub, map_sub, H.moments T d, G.moments T d, sub_zero]

private theorem Window.const_mul {n : ℕ} {P : K[X]} (H : Window n P) (s : K) :
    Window n (C s * P) := by
  refine ⟨(natDegree_C_mul_le s P).trans H.degree, ?_, ?_, ?_⟩
  · simp only [eval_mul, H.origin, mul_zero]
  · simp only [derivative_mul, derivative_C, zero_mul, zero_add,
      eval_mul, H.origin_derivative, mul_zero]
  · intro T d
    rw [mul_left_comm, ← Polynomial.smul_eq_C_mul, map_smul, H.moments T d, smul_zero]

variable [CharZero K]

private theorem integral01_derivative (P : K[X]) :
    integral01 P.derivative = P.eval 1 - P.eval 0 := by
  let S := P-C (P.eval 0)
  have s0 : S.coeff 0 = 0 := by
    rw [coeff_zero_eq_eval_zero]
    simp [S]
  have sd : S.derivative = P.derivative := by
    simp only [S, derivative_sub, derivative_C, sub_zero]
  change (primitive P.derivative).eval 1 = _
  rw [← sd, primitive_derivative S s0]
  simp only [S, eval_sub, eval_C]

/-- The first n moments detect degree ≤ n+1 when both origin values vanish.
Only the fixed Cauchy matrix with offset 3 is used. -/
theorem Window.eq_zero_of_lower_degree {n : ℕ} {P : K[X]} (H : Window n P)
    (d : P.natDegree ≤ n+1) : P = 0 := by
  classical
  by_contra hp
  have c0 : P.coeff 0 = 0 := (coeff_zero_eq_eval_zero P).trans H.origin
  have c1 : P.coeff 1 = 0 := by
    have e := H.origin_derivative
    rw [← coeff_zero_eq_eval_zero, coeff_derivative] at e
    simpa only [Nat.zero_add, Nat.cast_zero, zero_add, Nat.cast_one, mul_one] using e
  have dvd2 : (X : K[X])^2 ∣ P := X_pow_dvd_iff.mpr (fun k hk => by
    rcases (show k = 0 ∨ k = 1 by omega) with h | h
    · simpa only [h] using c0
    · simpa only [h] using c1)
  obtain ⟨S, hS⟩ := dvd2
  have S0 : S ≠ 0 := by
    intro e
    apply hp
    simp only [hS, e, mul_zero]
  have dS : S.natDegree < n := by
    rw [hS, natDegree_X_pow_mul 2 S0] at d
    omega
  let x : Fin n → K := fun i => (i.val : K)
  let y : Fin n → K := fun j => ((j.val + 3 : ℕ) : K)
  have hx : Function.Injective x := by
    intro i j e
    exact Fin.ext (Nat.cast_injective (R:=K) e)
  have hy : Function.Injective y := by
    intro i j e
    have h : i.val + 3 = j.val + 3 := Nat.cast_injective (R:=K) e
    exact Fin.ext (by omega)
  have hxy (i j : Fin n) : x i + y j ≠ 0 := by
    change (i.val : K) + ((j.val + 3 : ℕ) : K) ≠ 0
    rw [← Nat.cast_add]
    exact Nat.cast_ne_zero.mpr (by omega)
  have test (i : Fin n) : (∑ j : Fin n, S.coeff j.val / (x i+y j))=0 := by
    have m := H.moments (X^(i.val))
      ((natDegree_X_pow_le (R:=K) i.val).trans_lt i.isLt)
    rw [hS, ← mul_assoc, ← pow_add, integral01_power_mul_coeff dS] at m
    calc
      _ = ∑ j : Fin n, S.coeff j.val / ((j.val+(i.val+2)+1 : ℕ) : K) := by
        apply Finset.sum_congr rfl
        intro j _
        have e : x i + y j = ((j.val + (i.val + 2) + 1 : ℕ) : K) := by
          change (i.val : K) + ((j.val + 3 : ℕ) : K) = _
          rw [← Nat.cast_add]
          exact congrArg (fun k : ℕ => (k : K)) (by omega)
        rw [e]
      _ = 0 := m
  have van := cauchy_kernel x y (fun j => S.coeff j.val) hx hy hxy test
  have Sz : S = 0 := by
    ext j
    rw [coeff_zero]
    by_cases hj : j < n
    · exact van ⟨j,hj⟩
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
  exact S0 Sz

omit [CharZero K] in
private theorem degree_lower {n : ℕ} {P : K[X]} (h : P.natDegree ≤ n+2)
    (t : P.coeff (n+2) = 0) : P.natDegree ≤ n+1 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro k hk
  by_cases e : k = n+2
  · simpa only [e] using t
  · exact coeff_eq_zero_of_natDegree_lt (by omega)

private noncomputable def edgeWeight : K[X] := X*(1-X)

private noncomputable def differential (P : K[X]) : K[X] :=
  edgeWeight * P.derivative.derivative - P.derivative

omit [CharZero K] in
private theorem edgeWeight_degree : (edgeWeight : K[X]).natDegree ≤ 2 := by
  unfold edgeWeight
  apply natDegree_mul_le_of_le (m:=1) (n:=1)
  · simp
  · exact (natDegree_sub_le _ _).trans (by simp)

omit [CharZero K] in
private theorem edge_eval_zero : (edgeWeight : K[X]).eval 0 = 0 := by simp [edgeWeight]

omit [CharZero K] in
private theorem edge_eval_one : (edgeWeight : K[X]).eval 1 = 0 := by simp [edgeWeight]

omit [CharZero K] in
private theorem edge_deriv_eval_zero : (edgeWeight : K[X]).derivative.eval 0 = 1 := by
  simp [edgeWeight, derivative_mul, derivative_sub]

omit [CharZero K] in
private theorem edge_deriv_eval_one : (edgeWeight : K[X]).derivative.eval 1 = -1 := by
  simp [edgeWeight, derivative_mul, derivative_sub]

/-- One exact formal integration by parts, with both endpoint terms zero. -/
private theorem adjoint_test {P : K[X]} (h0 : P.eval 0 = 0) (T : K[X]) :
    integral01 (T * differential P) =
      integral01 (((edgeWeight*T).derivative.derivative + T.derivative)*P) := by
  let U := (edgeWeight : K[X])*T
  let B := U*P.derivative - (U.derivative+T)*P
  have u0 : U.eval 0 = 0 := by simp only [U, eval_mul, edge_eval_zero, zero_mul]
  have u1 : U.eval 1 = 0 := by simp only [U, eval_mul, edge_eval_one, zero_mul]
  have uD1 : U.derivative.eval 1 = -T.eval 1 := by
    simp only [U, derivative_mul, eval_add, eval_mul, edge_deriv_eval_one,
      edge_eval_one, neg_one_mul, zero_mul, add_zero]
  have b0 : B.eval 0 = 0 := by
    simp only [B, eval_sub, eval_mul, u0, h0, zero_mul, mul_zero, sub_zero]
  have b1 : B.eval 1 = 0 := by
    simp only [B, eval_sub, eval_mul, eval_add, u1, uD1, neg_add_cancel, zero_mul, sub_zero]
  have eq : B.derivative =
      T*differential P - (U.derivative.derivative+T.derivative)*P := by
    simp only [B, differential, U, derivative_sub, derivative_mul, map_add] <;> ring
  have eI := integral01_derivative B
  rw [eq, map_sub, b0, b1, sub_zero] at eI
  exact sub_eq_zero.mp eI

private theorem adjoint_degree (T : K[X]) :
    ((edgeWeight*T).derivative.derivative+T.derivative).natDegree ≤ T.natDegree := by
  have hW := natDegree_mul_le_of_le (edgeWeight_degree (K:=K))
    (show T.natDegree ≤ T.natDegree from le_rfl)
  have h1 := natDegree_derivative_le ((edgeWeight : K[X])*T)
  have h2 := natDegree_derivative_le (((edgeWeight : K[X])*T).derivative)
  have hT := natDegree_derivative_le T
  exact (natDegree_add_le _ _).trans (max_le (by omega) (by omega))

private theorem Window.differential_mem {n : ℕ} {P : K[X]} (H : Window n P) :
    Window n (differential P) := by
  have hdeg := H.degree
  have d1 := natDegree_derivative_le P
  have d2 := natDegree_derivative_le P.derivative
  have dprod : ((edgeWeight : K[X])*P.derivative.derivative).natDegree ≤ n+2 :=
    (natDegree_mul_le_of_le (edgeWeight_degree (K:=K))
      (show P.derivative.derivative.natDegree ≤ n by omega)).trans (by omega)
  refine ⟨(natDegree_sub_le _ _).trans (max_le dprod (by omega)), ?_, ?_, ?_⟩
  · simp only [differential, eval_sub, eval_mul, edge_eval_zero, zero_mul, H.origin_derivative,
      sub_zero]
  · simp only [differential, derivative_sub, derivative_mul, eval_sub, eval_add, eval_mul,
      edge_deriv_eval_zero, edge_eval_zero, zero_mul, one_mul, add_zero, sub_self]
  · intro T dT
    rw [adjoint_test H.origin]
    exact H.moments _ ((adjoint_degree T).trans_lt dT)

/-- The preserved moment line supplies the second-order differential identity.
No explicit eigenvalue or Jacobi polynomial is needed. -/
theorem Window.exists_differential_scalar {n : ℕ} {P : K[X]} (H : Window n P) (hp : P ≠ 0) :
    ∃ s : K, (X*(1-X))*P.derivative.derivative = P.derivative + C s*P := by
  have top : P.coeff (n+2) ≠ 0 := fun z =>
    hp (H.eq_zero_of_lower_degree (degree_lower H.degree z))
  let s := (differential P).coeff (n+2) / P.coeff (n+2)
  let R := differential P-C s*P
  have HR : Window n R := H.differential_mem.sub (H.const_mul s)
  have rTop : R.coeff (n+2)=0 := by
    simp only [R, coeff_sub, coeff_C_mul, s]
    rw [div_mul_cancel₀ _ top, sub_self]
  have rz : R = 0 := HR.eq_zero_of_lower_degree (degree_lower HR.degree rTop)
  change differential P-C s*P=0 at rz
  have e : (X*(1-X))*P.derivative.derivative-P.derivative = C s*P :=
    sub_eq_zero.mp rz
  exact ⟨s, (sub_eq_iff_eq_add.mp e).trans (add_comm _ _)⟩

private theorem derivative_ne_zero_of_nonzero_root {P : K[X]} {u : K}
    (hp : P ≠ 0) (hu : P.eval u = 0) : P.derivative ≠ 0 := by
  intro dz
  have e := eq_C_of_derivative_eq_zero dz
  rw [e, eval_C] at hu
  exact hp (by rw [e, hu, C_0])

/-- A nonzero polynomial satisfying any regular second-order equation has
no stationary root away from the zeros of its highest derivative factor. -/
theorem derivative_eval_ne_zero_of_regular_eq {A B C₀ P : K[X]} {u : K}
    (hp : P ≠ 0) (eq : A*P.derivative.derivative=B*P.derivative+C₀*P)
    (reg : A.eval u ≠ 0) (hu : P.eval u = 0) :
    P.derivative.eval u ≠ 0 := by
  intro du
  have d0 := derivative_ne_zero_of_nonzero_root hp hu
  have dd0 := derivative_ne_zero_of_nonzero_root d0 du
  have a0 : A ≠ 0 := fun z => reg (by simp only [z, eval_zero])
  let m := P.rootMultiplicity u
  have two : 1 < m := (one_lt_rootMultiplicity_iff_isRoot hp).mpr ⟨hu,du⟩
  have m1 : P.derivative.rootMultiplicity u = m-1 :=
    derivative_rootMultiplicity_of_root (show P.IsRoot u from hu)
  have m2 : P.derivative.derivative.rootMultiplicity u = m-2 := by
    rw [derivative_rootMultiplicity_of_root (show P.derivative.IsRoot u from du), m1] <;> omega
  have dm : (X-C u)^(m-1) ∣ P :=
    (le_rootMultiplicity_iff hp).mp (show m-1≤m from Nat.sub_le _ _)
  have dd : (X-C u)^(m-1) ∣ P.derivative :=
    (le_rootMultiplicity_iff d0).mp (by simp only [m1, le_refl])
  have dprod : (X-C u)^(m-1) ∣ A*P.derivative.derivative := by
    rw [eq]
    exact dvd_add (dd.trans (dvd_mul_left _ _)) (dm.trans (dvd_mul_left _ _))
  have out := (le_rootMultiplicity_iff (mul_ne_zero a0 dd0)).mpr dprod
  have ma : A.rootMultiplicity u = 0 :=
    rootMultiplicity_eq_zero (show ¬ A.IsRoot u from reg)
  rw [rootMultiplicity_mul (mul_ne_zero a0 dd0), ma, m2, zero_add] at out
  omega

/-- Any root in the regular part of the unit clock is simple. The statement
holds over all characteristic-zero fields, not only ordered fields. -/
theorem Window.derivative_eval_ne_zero {n : ℕ} {P : K[X]} {u : K}
    (H : Window n P) (hp : P ≠ 0) (u0 : u ≠ 0) (u1 : u ≠ 1)
    (hu : P.eval u = 0) : P.derivative.eval u ≠ 0 := by
  obtain ⟨s,e⟩ := H.exists_differential_scalar hp
  have e' : (X*(1-X))*P.derivative.derivative = 1*P.derivative+C s*P := by
    simpa only [one_mul] using e
  refine derivative_eval_ne_zero_of_regular_eq hp e' ?_ hu
  simp only [eval_mul, eval_X, eval_sub, eval_one]
  exact mul_ne_zero u0 (sub_ne_zero.mpr u1.symm)

theorem Window.eval_ne_zero_of_derivative_zero {n : ℕ} {P : K[X]} {u : K}
    (H : Window n P) (hp : P ≠ 0) (u0 : u ≠ 0) (u1 : u ≠ 1)
    (du : P.derivative.eval u = 0) : P.eval u ≠ 0 :=
  fun hu => (H.derivative_eval_ne_zero hp u0 u1 hu) du

end RKResearch.Certified.Graded.OriginMomentDifferential
