module

public import RKCert.ReviewedNative.OriginMomentDifferential
import Mathlib.Tactic.Ring

@[expose] public section

/-! # The origin-moment differential criterion with bounded natural casts

An additive sibling of the checked characteristic-zero result. Only the
finite scalar casts used by the Cauchy tests, formal FTC, and the local
multiplicity argument are assumed. No new typeclass is introduced.
-/

namespace RKResearch.Certified.Graded.OriginMomentDifferential

open Polynomial
open scoped BigOperators

variable {K : Type*} [Field K]

/-- The positive natural scalars through a specified bound are nonzero.
Over a field this is exactly the corresponding finite unit condition. -/
def NatCastsThrough (K : Type*) [Field K] (D : ℕ) : Prop :=
  ∀ k : ℕ, 0 < k → k ≤ D → (k : K) ≠ 0

private theorem casts_mono {D E : ℕ} (hz : NatCastsThrough K E) (de : D ≤ E) :
    NatCastsThrough K D :=
  fun k kp kle => hz k kp (kle.trans de)

private theorem cast_eq_of_le {D i j : ℕ} (hz : NatCastsThrough K D)
    (hi : i ≤ D) (hj : j ≤ D) (e : (i : K) = (j : K)) : i = j := by
  have no_lt {a b : ℕ} (ab : a < b) (hb : b ≤ D) (h : (a : K) = (b : K)) : False := by
    apply hz (b-a) (Nat.sub_pos_of_lt ab) ((Nat.sub_le b a).trans hb)
    rw [Nat.cast_sub ab.le, h, sub_self]
  rcases lt_trichotomy i j with lt | same | gt
  · exact (no_lt lt hj e).elim
  · exact same
  · exact (no_lt gt hi e.symm).elim

private theorem integral01_monomial_for_casts (k : ℕ) (s : K) :
    integral01 (monomial k s) = s / ((k+1 : ℕ) : K) := by
  rw [integral01_apply, primitive_monomial, eval_monomial, one_pow, mul_one]

private theorem integral01_power_mul_coeff_for_casts {P : K[X]} {n : ℕ}
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
      rw [X_pow_mul_monomial, integral01_monomial_for_casts]

/-- The degree n+1 kernel is zero using the bounded Cauchy cast window. -/
theorem Window.eq_zero_of_lower_degree_of_casts {n : ℕ} {P : K[X]} (H : Window n P)
    (d : P.natDegree ≤ n+1) (hz : NatCastsThrough K (2*n+1)) : P = 0 := by
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
    have hi := i.isLt
    have hj := j.isLt
    exact Fin.ext (cast_eq_of_le (i:=i.val) (j:=j.val) hz (by omega) (by omega) e)
  have hy : Function.Injective y := by
    intro i j e
    have hi := i.isLt
    have hj := j.isLt
    have h := cast_eq_of_le (i:=i.val+3) (j:=j.val+3) hz (by omega) (by omega) e
    exact Fin.ext (by omega)
  have hxy (i j : Fin n) : x i + y j ≠ 0 := by
    have hi := i.isLt
    have hj := j.isLt
    change (i.val : K) + ((j.val + 3 : ℕ) : K) ≠ 0
    rw [← Nat.cast_add]
    exact hz _ (by omega) (by omega)
  have test (i : Fin n) : (∑ j : Fin n, S.coeff j.val / (x i+y j))=0 := by
    have m := H.moments (X^(i.val))
      ((natDegree_X_pow_le (R:=K) i.val).trans_lt i.isLt)
    rw [hS, ← mul_assoc, ← pow_add, integral01_power_mul_coeff_for_casts dS] at m
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

private theorem primitive_derivative_of_degree_casts {P : K[X]} {D : ℕ}
    (d : P.natDegree ≤ D) (p0 : P.coeff 0 = 0)
    (hz : NatCastsThrough K D) : primitive P.derivative = P := by
  ext k
  cases k with
  | zero => rw [primitive_coeff_zero, p0]
  | succ j =>
    rw [primitive_coeff_succ, coeff_derivative, ← Nat.cast_add_one]
    by_cases paid : j+1 ≤ D
    · exact mul_div_cancel_right₀ _ (hz (j+1) (Nat.succ_pos j) paid)
    · have outside : P.coeff (j+1) = 0 :=
        coeff_eq_zero_of_natDegree_lt (by omega)
      rw [outside, zero_mul, zero_div]

private theorem integral01_derivative_of_degree_casts {P : K[X]} {D : ℕ}
    (d : P.natDegree ≤ D) (hz : NatCastsThrough K D) :
    integral01 P.derivative = P.eval 1 - P.eval 0 := by
  let S := P-C (P.eval 0)
  have s0 : S.coeff 0 = 0 := by
    rw [coeff_zero_eq_eval_zero]
    simp [S]
  have sd : S.derivative = P.derivative := by
    simp only [S, derivative_sub, derivative_C, sub_zero]
  have bound : S.natDegree ≤ D := by
    change (P-C (P.eval 0)).natDegree ≤ D
    exact (natDegree_sub_le _ _).trans (max_le d (by simp))
  change (primitive P.derivative).eval 1 = _
  rw [← sd, primitive_derivative_of_degree_casts bound s0 hz]
  simp only [S, eval_sub, eval_C]

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

private theorem edgeWeight_degree : (edgeWeight : K[X]).natDegree ≤ 2 := by
  unfold edgeWeight
  apply natDegree_mul_le_of_le (m:=1) (n:=1)
  · simp
  · exact (natDegree_sub_le _ _).trans (by simp)

private theorem edge_eval_zero : (edgeWeight : K[X]).eval 0 = 0 := by simp [edgeWeight]

private theorem edge_eval_one : (edgeWeight : K[X]).eval 1 = 0 := by simp [edgeWeight]

private theorem edge_deriv_eval_zero : (edgeWeight : K[X]).derivative.eval 0 = 1 := by
  simp [edgeWeight, derivative_mul, derivative_sub]

private theorem edge_deriv_eval_one : (edgeWeight : K[X]).derivative.eval 1 = -1 := by
  simp [edgeWeight, derivative_mul, derivative_sub]

/-- One exact formal integration by parts, with both endpoint terms zero. -/
private theorem adjoint_test_of_casts {P : K[X]} {n : ℕ}
    (d : P.natDegree ≤ n+2) (h0 : P.eval 0 = 0)
    (hz : NatCastsThrough K (2*n+2)) (T : K[X]) (dT : T.natDegree < n) :
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
  have udeg : U.natDegree ≤ n+1 :=
    (natDegree_mul_le_of_le (edgeWeight_degree (K:=K))
      (show T.natDegree ≤ n-1 by omega)).trans (by omega)
  have ud' := natDegree_derivative_le U
  have pd' := natDegree_derivative_le P
  have ud : U.derivative.natDegree ≤ n := by omega
  have pd : P.derivative.natDegree ≤ n+1 := by omega
  have left_degree : (U*P.derivative).natDegree ≤ 2*n+2 :=
    (natDegree_mul_le_of_le udeg pd).trans (by omega)
  have sumdeg : (U.derivative+T).natDegree ≤ n :=
    (natDegree_add_le _ _).trans (max_le ud (by omega))
  have right_degree : ((U.derivative+T)*P).natDegree ≤ 2*n+2 :=
    (natDegree_mul_le_of_le sumdeg d).trans (by omega)
  have dB : B.natDegree ≤ 2*n+2 :=
    (natDegree_sub_le _ _).trans (max_le left_degree right_degree)
  have eI := integral01_derivative_of_degree_casts dB hz
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

private theorem Window.differential_mem_of_casts {n : ℕ} {P : K[X]}
    (H : Window n P) (hz : NatCastsThrough K (2*n+2)) :
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
    rw [adjoint_test_of_casts H.degree H.origin hz T dT]
    exact H.moments _ ((adjoint_degree T).trans_lt dT)

/-- The preserved moment line supplies the second-order differential identity.
No explicit eigenvalue or Jacobi polynomial is needed. -/
theorem Window.exists_differential_scalar_of_casts {n : ℕ} {P : K[X]}
    (H : Window n P) (hp : P ≠ 0) (hz : NatCastsThrough K (2*n+2)) :
    ∃ s : K, (X*(1-X))*P.derivative.derivative = P.derivative + C s*P := by
  have lower : NatCastsThrough K (2*n+1) := casts_mono hz (by omega)
  have top : P.coeff (n+2) ≠ 0 := fun z =>
    hp (H.eq_zero_of_lower_degree_of_casts (degree_lower H.degree z) lower)
  have HL := H.differential_mem_of_casts hz
  let s := (differential P).coeff (n+2) / P.coeff (n+2)
  let R := differential P-C s*P
  have HRd : R.natDegree ≤ n+2 :=
    (natDegree_sub_le _ _).trans (max_le HL.degree
      ((natDegree_C_mul_le s P).trans H.degree))
  have HR0 : R.eval 0 = 0 := by
    simp only [R, eval_sub, HL.origin, eval_mul, H.origin, mul_zero, sub_zero]
  have HR1 : R.derivative.eval 0 = 0 := by
    simp only [R, derivative_sub, HL.origin_derivative, derivative_mul,
      derivative_C, zero_mul, zero_add, eval_sub, eval_mul, H.origin_derivative,
      mul_zero, sub_zero]
  have HRtest (k : ℕ) (hk : k < n) : integral01 (X^k * R) = 0 := by
    have dk := (natDegree_X_pow_le (R:=K) k).trans_lt hk
    change integral01 (X^k * (differential P-C s*P)) = 0
    rw [mul_sub, map_sub, HL.moments _ dk]
    have shift : (X : K[X])^k * (C s * P) = C s * (X^k * P) := by
      rw [mul_left_comm]
    rw [shift, ← Polynomial.smul_eq_C_mul, map_smul, H.moments _ dk,
      smul_zero, sub_zero]
  have HR : Window n R := Window.of_power HRd HR0 HR1 HRtest
  have rTop : R.coeff (n+2)=0 := by
    simp only [R, coeff_sub, coeff_C_mul, s]
    rw [div_mul_cancel₀ _ top, sub_self]
  have rz : R = 0 := HR.eq_zero_of_lower_degree_of_casts (degree_lower HR.degree rTop) lower
  change differential P-C s*P=0 at rz
  have e : (X*(1-X))*P.derivative.derivative-P.derivative = C s*P :=
    sub_eq_zero.mp rz
  exact ⟨s, (sub_eq_iff_eq_add.mp e).trans (add_comm _ _)⟩

/-- In the regular ODE criterion, only the two casts at an alleged
multiple root are needed; no global injectivity of natural casts is used. -/
theorem derivative_eval_ne_zero_of_regular_eq_of_casts {A B C₀ P : K[X]} {u : K}
    (hp : P ≠ 0) (eq : A*P.derivative.derivative=B*P.derivative+C₀*P)
    (reg : A.eval u ≠ 0) (hu : P.eval u = 0)
    (paid : 1 < P.rootMultiplicity u →
      ((P.rootMultiplicity u : ℕ) : K) ≠ 0 ∧
        ((P.rootMultiplicity u - 1 : ℕ) : K) ≠ 0) :
    P.derivative.eval u ≠ 0 := by
  intro du
  have root : P.IsRoot u := hu
  have root' : P.derivative.IsRoot u := du
  let m := P.rootMultiplicity u
  have two : 1 < m := (one_lt_rootMultiplicity_iff_isRoot hp).mpr ⟨root,root'⟩
  obtain ⟨m0, pred0⟩ := paid two
  have m1 : P.derivative.rootMultiplicity u = m-1 :=
    derivative_rootMultiplicity_of_root_of_mem_nonZeroDivisors root
      (mem_nonZeroDivisors_of_ne_zero m0)
  have castD : (P.derivative.rootMultiplicity u : K) ≠ 0 := by
    rw [m1]
    exact pred0
  have m2 : P.derivative.derivative.rootMultiplicity u = m-2 := by
    rw [derivative_rootMultiplicity_of_root_of_mem_nonZeroDivisors root'
      (mem_nonZeroDivisors_of_ne_zero castD), m1] <;> omega
  have d0 : P.derivative ≠ 0 := by
    intro z
    have h := m1
    rw [z, rootMultiplicity_zero] at h
    omega
  have dd0 : P.derivative.derivative ≠ 0 := by
    intro z
    have root'' : P.derivative.derivative.IsRoot u := by
      simp only [z, Polynomial.IsRoot, eval_zero]
    have t := (one_lt_rootMultiplicity_iff_isRoot d0).mpr ⟨root',root''⟩
    rw [m1] at t
    have h := m2
    rw [z, rootMultiplicity_zero] at h
    omega
  have a0 : A ≠ 0 := fun z => reg (by simp only [z, eval_zero])
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

/-- A regular root of the moment-window polynomial is simple under the
finite natural cast condition through 2n+2. -/
theorem Window.derivative_eval_ne_zero_of_casts {n : ℕ} {P : K[X]} {u : K}
    (H : Window n P) (hp : P ≠ 0) (hz : NatCastsThrough K (2*n+2))
    (u0 : u ≠ 0) (u1 : u ≠ 1) (hu : P.eval u = 0) :
    P.derivative.eval u ≠ 0 := by
  obtain ⟨s,e⟩ := H.exists_differential_scalar_of_casts hp hz
  have e' : (X*(1-X))*P.derivative.derivative = 1*P.derivative+C s*P := by
    simpa only [one_mul] using e
  have reg : ((X*(1-X)) : K[X]).eval u ≠ 0 := by
    simp only [eval_mul, eval_X, eval_sub, eval_one]
    exact mul_ne_zero u0 (sub_ne_zero.mpr u1.symm)
  refine derivative_eval_ne_zero_of_regular_eq_of_casts hp e' reg hu (fun hm => ?_)
  have md : P.rootMultiplicity u ≤ P.natDegree := by
    simpa only [natDegree_pow, natDegree_X_sub_C, mul_one] using
      natDegree_le_of_dvd (pow_rootMultiplicity_dvd P u) hp
  have hd := H.degree
  exact ⟨hz _ (by omega) (by omega), hz _ (by omega) (by omega)⟩

theorem Window.eval_ne_zero_of_derivative_zero_of_casts {n : ℕ} {P : K[X]} {u : K}
    (H : Window n P) (hp : P ≠ 0) (hz : NatCastsThrough K (2*n+2))
    (u0 : u ≠ 0) (u1 : u ≠ 1) (du : P.derivative.eval u = 0) :
    P.eval u ≠ 0 :=
  fun hu => (H.derivative_eval_ne_zero_of_casts hp hz u0 u1 hu) du

end RKResearch.Certified.Graded.OriginMomentDifferential
