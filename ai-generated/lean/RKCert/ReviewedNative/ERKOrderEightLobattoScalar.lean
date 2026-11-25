module

public import RKCert.NodalPrimitive
public import RKCert.ReviewedNative.GradedPrimitives

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Pure cubic Lobatto identities for the order-eight census

The statements are polynomial only. The published scalar proof slices use
the reviewed zero-constant `Graded.primitive` here directly: its monomial
formula agrees with the formula used by the published scalar calculation.
No legacy tableau or order predicate is imported.
-/
namespace RKResearch.Certified.Graded.LobattoEight

open Polynomial RKCert.Endpoint
open scoped Classical

variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
theorem nodalHull_erase_factor (T : Finset K) {a : K} (ha : a∈T) :
    nodalHull T = (X-C a)*nodalHull (T.erase a) := by
  unfold nodalHull
  exact (Finset.mul_prod_erase T _ ha).symm

omit [CharZero K] in
theorem nodalHull_two_endpoint_factor (T : Finset K) (h0 : (0:K)∈T) (h1 : (1:K)∈T) :
    nodalHull T = (X^2-X)*nodalHull ((T.erase 1).erase 0) := by
  rw [nodalHull_erase_factor T h1,nodalHull_erase_factor (T.erase 1)
    (Finset.mem_erase.mpr ⟨zero_ne_one,h0⟩)]
  simp only [map_one,map_zero,sub_zero]
  ring

omit [CharZero K] in
theorem nodalHull_eval_ne_zero_of_notMem {T : Finset K} {u : K} (hu : u∉T) :
    (nodalHull T).eval u≠0 := by
  simp only [nodalHull,eval_prod,eval_sub,eval_X,eval_C]
  exact Finset.prod_ne_zero_iff.mpr (fun a ha => sub_ne_zero.mpr (fun h => hu (h.symm ▸ ha)))

omit [CharZero K] in
theorem quadratic_coeff_expand (P : K[X]) (hp : P.natDegree ≤ 2) :
    P = monomial 0 (P.coeff 0) + monomial 1 (P.coeff 1) + monomial 2 (P.coeff 2) := by
  nth_rw 1 [P.as_sum_range' 3 (by omega)]
  simp [Finset.sum_range_succ]

omit [CharZero K] in
theorem primitive_eval_quadratic (P : K[X]) (hp : P.natDegree ≤ 2) (u : K) :
    (primitive P).eval u = P.coeff 0*u + P.coeff 1*u^2/2 + P.coeff 2*u^3/3 := by
  conv_lhs => rw [quadratic_coeff_expand P hp]
  simp only [map_add,primitive_monomial,eval_add,eval_monomial,Nat.reduceAdd,Nat.cast_one,
    div_one,pow_one,Nat.cast_ofNat,div_mul_eq_mul_div]

omit [CharZero K] in
theorem primitive_eval_X_quadratic (P : K[X]) (hp : P.natDegree ≤ 2) (u : K) :
    (primitive (X*P)).eval u = P.coeff 0*u^2/2 + P.coeff 1*u^3/3 + P.coeff 2*u^4/4 := by
  conv_lhs => rw [quadratic_coeff_expand P hp]
  simp only [mul_add,X_mul_monomial,map_add,primitive_monomial,eval_add,eval_monomial,
    Nat.reduceAdd,Nat.cast_ofNat,div_mul_eq_mul_div]

noncomputable def lobattoCubic : K[X] :=
  monomial 0 (-1/14) + monomial 1 (9/14) + monomial 2 (-3/2) + monomial 3 1

set_option maxHeartbeats 600000 in
theorem lobatto_cubic_decoder (Q : K[X]) (hd : Q.natDegree ≤ 3)
    (hm : ∀ i : Fin 3,
      (∑ j : Fin 4, Q.coeff j.val / ((i.val+j.val+3:ℕ):K)) -
      (∑ j : Fin 4, Q.coeff j.val / ((i.val+j.val+2:ℕ):K))=0) :
    Q = C (Q.coeff 3) * lobattoCubic := by
  have h0 := hm 0
  have h1 := hm 1
  have h2 := hm 2
  norm_num [Fin.sum_univ_succ] at h0 h1 h2
  have hQ0 : Q.coeff 0 = Q.coeff 3*(-1/14) := by linear_combination -120*h0 + 480*h1 - 420*h2
  have hQ1 : Q.coeff 1 = Q.coeff 3*(9/14) := by linear_combination 480*h0 - 2220*h1 + 2100*h2
  have hQ2 : Q.coeff 2 = Q.coeff 3*(-3/2) := by linear_combination -420*h0 + 2100*h1 - 2100*h2
  ext n
  by_cases h : n≤3
  · interval_cases n <;> simp [coeff_C_mul,lobattoCubic,coeff_monomial,hQ0,hQ1,hQ2]
  · rw [coeff_eq_zero_of_natDegree_lt (by omega : Q.natDegree < n),coeff_C_mul]
    simp only [lobattoCubic,coeff_add,coeff_monomial]
    have h0' : 0≠n := by omega
    have h1' : 1≠n := by omega
    have h2' : 2≠n := by omega
    have h3' : 3≠n := by omega
    simp [h0',h1',h2',h3']

omit [CharZero K] in
theorem lobatto_isRoot_of_linear {P : K[X]} {u : K}
    (h : lobattoCubic = (X-C u)*P) : lobattoCubic.eval u=0 := by rw [h]; simp

set_option maxHeartbeats 400000 in
/-- The first physical clean node is excluded when its omitted
quadratic factor is the other two roots of the order-eight Lobatto cubic. -/
theorem lobatto_first_on_scalar_gate {P : K[X]} (hP : P.natDegree≤2)
    {u : K} (hu : u≠0) (h : lobattoCubic = (X-C u)*P)
    (hprim : (primitive (X*P)).eval u=0) : False := by
  have h0 := lobatto_isRoot_of_linear h
  have hr : 14*u^3 - 21*u^2 + 9*u - 1 = 0 := by
    simp [lobattoCubic] at h0
    linear_combination 14*h0
  have hcoef (n : ℕ) : (lobattoCubic : K[X]).coeff (n+1) =
      P.coeff n - u*P.coeff (n+1) := by
    rw [h,sub_mul,coeff_sub,coeff_X_mul,coeff_C_mul]
  have h3 := hcoef 2
  have h2 := hcoef 1
  have h1 := hcoef 0
  have hz : P.coeff 3=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  norm_num [lobattoCubic,coeff_monomial,hz] at h3 h2 h1
  rw [primitive_eval_X_quadratic P hP] at hprim
  have hq : u^2 * (91*u^2 - 105*u + 27)=0 := by
    linear_combination 84*hprim + 91*u^4*h3 + 70*u^3*h2 + 42*u^2*h1
  have hg := (mul_eq_zero.mp hq).resolve_left (pow_ne_zero _ hu)
  have hbad : (1:K)=0 := by
    linear_combination (232/11-819*u/22)*hr + (63*u^2/11-115*u/22+9/11)*hg
  exact one_ne_zero hbad

theorem lobattoCubic_degree : (lobattoCubic : K[X]).natDegree=3 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    have hi0 : 0≠i := by omega
    have hi1 : 1≠i := by omega
    have hi2 : 2≠i := by omega
    have hi3 : 3≠i := by omega
    simp [lobattoCubic,coeff_monomial,coeff_C,Ne.symm hi0,hi1,hi2,hi3]
  · simp [lobattoCubic,coeff_monomial]

/-- A quadratic divisor of the fixed cubic leaves one exact linear
factor, with no ordering on roots needed. -/
theorem lobatto_divisor_linear_factor {P : K[X]} (hd : P.natDegree=2)
    (hdiv : P∣lobattoCubic) :
    ∃ u a : K, a≠0 ∧ lobattoCubic = (X-C u)*(C a*P) := by
  obtain ⟨R,he⟩ := hdiv
  have hn : (lobattoCubic : K[X])≠0 := by
    intro h; have hd := lobattoCubic_degree (K:=K); simp [h] at hd
  have hR : R≠0 := by intro h; apply hn; simp [he,h]
  have hP : P≠0 := by intro h; apply hn; simp [he,h]
  have hdeg := natDegree_mul hP hR
  rw [←he,lobattoCubic_degree,hd] at hdeg
  obtain ⟨a,ha,b,hb⟩ := Polynomial.natDegree_eq_one.mp (by omega : R.natDegree=1)
  let u := -b/a
  have hconst : -(a*u)=b := by
    dsimp [u]
    field_simp [ha]
  have hR' : R=(X-C u)*C a := by
    rw [←hb,sub_mul,mul_comm X,←map_mul,mul_comm u a,sub_eq_add_neg,← map_neg,hconst]
  exact ⟨u,a,ha,by rw [he,hR']; ring⟩

end RKResearch.Certified.Graded.LobattoEight
