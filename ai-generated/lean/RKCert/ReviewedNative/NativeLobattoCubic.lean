module

public import RKCert.ReviewedNative.NativeLobatto43
public import RKCert.ReviewedNative.GradedPrimitives

import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # The five early Lobatto cubic ports, including the true shared leakage

The two moments at the first knot leave a two-dimensional coefficient
plane. The mixed low moment and the two mixed high moments eliminate that
plane by a small cleared residue minor. This is separate from physical
stage transport. -/

namespace RKResearch.Certified.Graded.NativeLobatto

open Polynomial
open scoped BigOperators

variable {K : Type*} [Field K] [CharZero K]

private def cubicI1 (a b c d z : K) : K :=
  a*z^2/2 + b*z^3/3 + c*z^4/4 + d*z^5/5

private def cubicI2 (a b c d z : K) : K :=
  a*z^3/3 + b*z^4/4 + c*z^5/5 + d*z^6/6

private def cubicI3 (a b c d z : K) : K :=
  a*z^4/4 + b*z^5/5 + c*z^6/6 + d*z^7/7

set_option maxHeartbeats 1000000 in
private theorem normalized_cubic_coefficients_zero (a b c d z k j₀ j₁ : K)
    (z0 : z≠0) (z1 : z≠1)
    (minor : cubicD z*j₁ + z^4*cubicN z*j₀ ≠ 0)
    (h1 : cubicI1 a b c d 1=0)
    (h2 : cubicI2 a b c d 1=0)
    (h3 : cubicI3 a b c d 1=k*j₀)
    (h4 : cubicI2 a b c d z-cubicI1 a b c d z=0)
    (h5 : cubicI3 a b c d z-cubicI2 a b c d z=k*j₁) :
    a=0 ∧ b=0 ∧ c=0 ∧ d=0 := by
  unfold cubicI1 at h1 h4
  unfold cubicI2 at h2 h4 h5
  unfold cubicI3 at h3 h5
  have aeq : a = (3/10:K)*c + (2/5:K)*d := by
    linear_combination 18*h1 - 24*h2
  have beq : b = -(6/5:K)*c - (6/5:K)*d := by
    linear_combination -24*h1 + 36*h2
  rw [aeq,beq] at h3 h4 h5
  let L : K := 3*(4*z-3)
  let M : K := 2*(5*z^2+4*z-6)
  have small : L*c+M*d=0 := by
    have f : (z^2*(z-1)^2)*(L*c+M*d)=0 := by
      dsimp only [L,M]
      linear_combination 60*h4
    exact (mul_eq_zero.mp f).resolve_left
      (mul_ne_zero (pow_ne_zero _ z0) (pow_ne_zero _ (sub_ne_zero.mpr z1)))
  let A : K := (j₁-j₀*z^3*(100*z^3-264*z^2+225*z-60))/600
  let B : K := j₁/350-j₀*z^3*(150*z^4-175*z^3-252*z^2+420*z-140)/1050
  have high : A*c+B*d=0 := by
    dsimp only [A,B]
    linear_combination j₁*h3 - j₀*h5
  have det : L*B-M*A = -((cubicD z*j₁+z^4*cubicN z*j₀)/2100) := by
    dsimp only [L,M,A,B,cubicD,cubicN]
    ring
  have det0 : L*B-M*A≠0 := by
    rw [det]
    exact neg_ne_zero.mpr (div_ne_zero minor (by norm_num))
  have ce : c=0 := by
    have f : (L*B-M*A)*c=0 := by linear_combination B*small - M*high
    exact (mul_eq_zero.mp f).resolve_left det0
  have de : d=0 := by
    have f : (L*B-M*A)*d=0 := by linear_combination L*high - A*small
    exact (mul_eq_zero.mp f).resolve_left det0
  exact ⟨by simpa [ce,de] using aeq, by simpa [ce,de] using beq, ce, de⟩

private theorem cubic_moment_sum (P : K[X]) (pd : P.natDegree ≤ 3) (x : K) (k : ℕ) :
    (primitive ((X:K[X])^k*P)).eval x =
      ∑ i : Fin 4, P.coeff i.val * x^(i.val+k+1) / ((i.val+k+1:ℕ):K) := by
  classical
  let a : Fin 4 → K := toFn 4 P
  have rep : ofFn 4 a = P := ofFn_comp_toFn_eq_id_of_natDegree_lt (Nat.lt_succ_of_le pd)
  calc
    _ = (primitive ((X:K[X])^k*ofFn 4 a)).eval x := by rw [rep]
    _ = _ := by
      rw [ofFn_eq_sum_monomial, Finset.mul_sum, map_sum, eval_finsetSum]
      apply Finset.sum_congr rfl
      intro i _
      rw [X_pow_mul_monomial, primitive_monomial, eval_monomial]
      have eq : a i = P.coeff i.val := rfl
      rw [eq]
      ring

private theorem cubic_moment_one (P : K[X]) (pd : P.natDegree≤3) (x : K) :
    (primitive (X*P)).eval x =
      cubicI1 (P.coeff 0) (P.coeff 1) (P.coeff 2) (P.coeff 3) x := by
  have e := cubic_moment_sum P pd x 1
  norm_num [Fin.sum_univ_succ, add_assoc] at e
  simpa only [cubicI1, pow_one, add_assoc] using e

private theorem cubic_moment_two (P : K[X]) (pd : P.natDegree≤3) (x : K) :
    (primitive (X^2*P)).eval x =
      cubicI2 (P.coeff 0) (P.coeff 1) (P.coeff 2) (P.coeff 3) x := by
  have e := cubic_moment_sum P pd x 2
  norm_num [Fin.sum_univ_succ, add_assoc] at e
  simpa only [cubicI2, pow_one, add_assoc] using e

private theorem cubic_moment_three (P : K[X]) (pd : P.natDegree≤3) (x : K) :
    (primitive (X^3*P)).eval x =
      cubicI3 (P.coeff 0) (P.coeff 1) (P.coeff 2) (P.coeff 3) x := by
  have e := cubic_moment_sum P pd x 3
  norm_num [Fin.sum_univ_succ, add_assoc] at e
  simpa only [cubicI3, pow_one, add_assoc] using e

set_option maxHeartbeats 1400000 in
/-- The actual five scalar equations from the two early Lobatto ports,
with one arbitrary shared highest-mask leakage. This lemma assumes no
tableau hypotheses or order on the field. -/
theorem cubic_profile_zero_of_lobatto_ports (P : K[X]) (pd : P.natDegree≤3)
    (t u k : K) (ht : lobattoValue t=0) (hu : lobattoValue u=0) (distinct : t≠u)
    (h1 : (primitive (X*P)).eval t=0)
    (h2 : (primitive (X^2*P)).eval t=0)
    (h3 : (primitive (X^3*P)).eval t=k*radauValue t)
    (h4 : (primitive (X^2*P)).eval u-t*(primitive (X*P)).eval u=0)
    (h5 : (primitive (X^3*P)).eval u-t*(primitive (X^2*P)).eval u=k*radauValue u) :
    P=0 := by
  classical
  have tn := lobatto_root_ne_zero ht
  have un := lobatto_root_ne_zero hu
  let z := u/t
  let η := k/t^4
  let a := P.coeff 0
  let b := P.coeff 1
  let c := P.coeff 2
  let d := P.coeff 3
  have z0 : z≠0 := div_ne_zero un tn
  have z1 : z≠1 := by
    intro e
    exact distinct (((div_eq_iff tn).mp e).trans (one_mul _)).symm
  have e1 (x : K) :
      cubicI1 a (b*t) (c*t^2) (d*t^3) (x/t) = cubicI1 a b c d x/t^2 := by
    unfold cubicI1
    field_simp [tn] <;> ring
  have e2 (x : K) :
      cubicI2 a (b*t) (c*t^2) (d*t^3) (x/t) = cubicI2 a b c d x/t^3 := by
    unfold cubicI2
    field_simp [tn] <;> ring
  have e3 (x : K) :
      cubicI3 a (b*t) (c*t^2) (d*t^3) (x/t) = cubicI3 a b c d x/t^4 := by
    unfold cubicI3
    field_simp [tn] <;> ring
  have base1 (x : K) : cubicI1 a b c d x=(primitive (X*P)).eval x :=
    (cubic_moment_one P pd x).symm
  have base2 (x : K) : cubicI2 a b c d x=(primitive (X^2*P)).eval x :=
    (cubic_moment_two P pd x).symm
  have base3 (x : K) : cubicI3 a b c d x=(primitive (X^3*P)).eval x :=
    (cubic_moment_three P pd x).symm
  have p1 : cubicI1 a (b*t) (c*t^2) (d*t^3) 1=0 := by
    rw [← div_self tn, e1, base1, h1, zero_div]
  have p2 : cubicI2 a (b*t) (c*t^2) (d*t^3) 1=0 := by
    rw [← div_self tn, e2, base2, h2, zero_div]
  have p3 : cubicI3 a (b*t) (c*t^2) (d*t^3) 1=η*radauValue t := by
    rw [← div_self tn, e3, base3, h3, mul_div_right_comm]
  have mix (A B : K) (n : ℕ) : A/t^(n+1)-B/t^n=(A-t*B)/t^(n+1) := by
    rw [pow_succ]
    field_simp [tn,pow_ne_zero n tn] <;> ring
  have p4 : cubicI2 a (b*t) (c*t^2) (d*t^3) z -
      cubicI1 a (b*t) (c*t^2) (d*t^3) z=0 := by
    dsimp only [z]
    rw [e2,e1,base2,base1]
    rw [mix ((primitive (X^2*P)).eval u) ((primitive (X*P)).eval u) 2, h4, zero_div]
  have p5 : cubicI3 a (b*t) (c*t^2) (d*t^3) z -
      cubicI2 a (b*t) (c*t^2) (d*t^3) z=η*radauValue u := by
    dsimp only [z]
    rw [e3,e2,base3,base2]
    rw [mix ((primitive (X^3*P)).eval u) ((primitive (X^2*P)).eval u) 3, h5, mul_div_right_comm]
  have minor : cubicD z*radauValue u+z^4*cubicN z*radauValue t≠0 :=
    normalized_cubic_minor_ne_zero t u ht hu distinct
  obtain ⟨ha,hb,hc,hd⟩ := normalized_cubic_coefficients_zero
    a (b*t) (c*t^2) (d*t^3) z η (radauValue t) (radauValue u) z0 z1 minor p1 p2 p3 p4 p5
  have hb0 : b=0 := (mul_eq_zero.mp hb).resolve_right tn
  have hc0 : c=0 := (mul_eq_zero.mp hc).resolve_right (pow_ne_zero _ tn)
  have hd0 : d=0 := (mul_eq_zero.mp hd).resolve_right (pow_ne_zero _ tn)
  have all : toFn 4 P=0 := by
    funext i
    fin_cases i
    · exact ha
    · exact hb0
    · exact hc0
    · exact hd0
  have rep : ofFn 4 (toFn 4 P)=P := ofFn_comp_toFn_eq_id_of_natDegree_lt (Nat.lt_succ_of_le pd)
  rw [all,map_zero] at rep
  exact rep.symm

end RKResearch.Certified.Graded.NativeLobatto
