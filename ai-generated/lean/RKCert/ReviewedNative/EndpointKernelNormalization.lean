module

public import RKCert.ReviewedNative.GradedPrimitives
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Exact endpoint normalization by one Cauchy coefficient

Clearing denominators of a constant Cauchy system identifies one monic
hull difference. Its next coefficient gives the sum of the solution.
No positivity, explicit orthogonal basis, or root-location theorem is used. -/
namespace RKResearch.Certified.Graded

open Polynomial
open scoped BigOperators

noncomputable section

variable {K : Type*} [Field K]

private theorem plusProd_natDegree {ι : Type*} (S : Finset ι) (y : ι → K) :
    (∏ i ∈ S, (X+C (y i))).natDegree = S.card := by
  rw [natDegree_prod_of_monic S _ (fun i _ => monic_X_add_C (y i))]
  simp [natDegree_X_add_C]

/-- Sum readout for a constant Cauchy system. Only the test nodes need to
be distinct. Repeated pole parameters are allowed if there is a solution. -/
theorem cauchy_constant_solution_sum {n : ℕ} (x y a : Fin (n+1) → K) (c : K)
    (hx : Function.Injective x) (den : ∀ i j, x i + y j ≠ 0)
    (tests : ∀ i, (∑ j : Fin (n+1), a j / (x i + y j)) = c) :
    (∑ j : Fin (n+1), a j) = c * ((∑ i, x i) + ∑ j, y j) := by
  classical
  let S : Finset (Fin (n+1)) := Finset.univ
  let D : K[X] := ∏ i ∈ S, (X+C (y i))
  let H : K[X] := ∏ i ∈ S, (X-C (x i))
  let G (j : Fin (n+1)) : K[X] := ∏ i ∈ S.erase j, (X+C (y i))
  let P : K[X] := ∑ j ∈ S, C (a j) * G j
  let Q : K[X] := C c * (D-H) - P
  have cardS : S.card = n+1 := by simp [S]
  have dD : D.natDegree = n+1 := (plusProd_natDegree S y).trans cardS
  have dH : H.natDegree = n+1 := by
    change (∏ i ∈ S, (X-C (x i))).natDegree = n+1
    rw [natDegree_prod_of_monic S _ (fun i _ => monic_X_sub_C (x i))]
    simp [natDegree_X_sub_C, cardS]
  have mD : D.Monic := monic_prod_of_monic S _ (fun i _ => monic_X_add_C (y i))
  have mH : H.Monic := monic_prod_X_sub_C x S
  have dG (j : Fin (n+1)) : (G j).natDegree = n := by
    change (∏ i ∈ S.erase j, (X+C (y i))).natDegree = n
    rw [plusProd_natDegree, Finset.card_erase_of_mem (show j ∈ S from Finset.mem_univ j),
      cardS, Nat.add_sub_cancel]
  have cG (j : Fin (n+1)) : (G j).coeff n = 1 := by
    have g : (G j).Monic :=
      monic_prod_of_monic (S.erase j) _ (fun i _ => monic_X_add_C (y i))
    rw [← dG j, g.coeff_natDegree]
  have dDH : (D-H).natDegree ≤ n := by
    by_cases z : D-H = 0
    · simp [z]
    · have d : D.degree = H.degree := by
        rw [degree_eq_natDegree mD.ne_zero, degree_eq_natDegree mH.ne_zero, dD, dH]
      have e := natDegree_lt_natDegree z
        (degree_sub_lt_left d mD.ne_zero (mD.leadingCoeff.trans mH.leadingCoeff.symm))
      rw [dD] at e
      exact Nat.le_of_lt_succ e
  have dP : P.natDegree ≤ n := by
    change (∑ j ∈ S, C (a j) * G j).natDegree ≤ n
    apply natDegree_sum_le_of_forall_le
    intro j _
    exact (natDegree_C_mul_le _ _).trans (dG j).le
  have dQ : Q.natDegree ≤ n := by
    have z := (natDegree_C_mul_le c (D-H)).trans dDH
    simpa only [Q, max_self] using natDegree_sub_le_of_le z dP
  have fac (i j : Fin (n+1)) :
      (G j).eval (x i) * (x i+y j) = D.eval (x i) := by
    simp only [G, D, eval_prod, eval_add, eval_X, eval_C]
    exact Finset.prod_erase_mul S _ (show j ∈ S from Finset.mem_univ j)
  have eP (i : Fin (n+1)) : P.eval (x i) = D.eval (x i) * c := by
    simp only [P, eval_finsetSum, eval_mul, eval_C]
    have pull (j : Fin (n+1)) (_ : j ∈ S) :
        a j * (G j).eval (x i) = D.eval (x i) * (a j / (x i+y j)) := by
      have q : (G j).eval (x i) = D.eval (x i) / (x i+y j) :=
        (eq_div_iff (den i j)).mpr (fac i j)
      rw [q]
      simp only [div_eq_mul_inv]
      ac_rfl
    rw [Finset.sum_congr rfl pull, ← Finset.mul_sum]
    change D.eval (x i) * (∑ j : Fin (n+1), a j / (x i+y j)) = _
    rw [tests i]
  have eH (i : Fin (n+1)) : H.eval (x i) = 0 := by
    simp only [H, eval_prod, eval_sub, eval_X, eval_C]
    exact Finset.prod_eq_zero (show i ∈ S from Finset.mem_univ i) (sub_self _)
  have roots (i : Fin (n+1)) : Q.eval (x i) = 0 := by
    change (C c * (D-H) - P).eval (x i) = 0
    simp only [eval_sub, eval_mul, eval_C, eH i, eP i, sub_zero]
    rw [mul_comm c (D.eval (x i)), sub_self]
  have q0 : Q = 0 :=
    eq_zero_of_natDegree_lt_card_of_eval_eq_zero Q hx roots (by
      rw [Fintype.card_fin]
      omega)
  have posS : 0 < S.card := by
    rw [cardS]
    exact Nat.succ_pos n
  have edge : S.card - 1 = n := by rw [cardS, Nat.add_sub_cancel]
  have hn : H.coeff n = -(∑ i : Fin (n+1), x i) := by
    have z := prod_X_sub_C_coeff_card_pred S x posS
    rw [edge] at z
    exact z
  have dn : D.coeff n = ∑ i : Fin (n+1), y i := by
    have negProd : (∏ i ∈ S, (X-C (-y i))) = D := by
      simp only [D, sub_eq_add_neg, C_neg, neg_neg]
    have z := prod_X_sub_C_coeff_card_pred S (fun i => -y i) posS
    rw [edge, negProd, Finset.sum_neg_distrib, neg_neg] at z
    exact z
  have pn : P.coeff n = ∑ i : Fin (n+1), a i := by
    simp only [P, finsetSum_coeff, coeff_C_mul, cG, mul_one, S]
  have z : c * ((∑ i : Fin (n+1), y i) - -(∑ i : Fin (n+1), x i)) -
      (∑ i : Fin (n+1), a i) = 0 := by
    simpa only [Q, coeff_sub, coeff_C_mul, dn, hn, pn, coeff_zero] using
      congrArg (fun f : K[X] => f.coeff n) q0
  calc
    (∑ i : Fin (n+1), a i) = c * ((∑ i, y i) - -(∑ i, x i)) :=
      (sub_eq_zero.mp z).symm
    _ = c * ((∑ i, x i) + ∑ i, y i) := by
      rw [sub_neg_eq_add, add_comm (∑ i : Fin (n+1), y i) (∑ i : Fin (n+1), x i)]

private theorem primitive_powerMoment_as_cauchy {n : ℕ} (R : K[X])
    (degree : R.natDegree ≤ n) (m k : ℕ) :
    (primitive (X^m*R*X^k)).eval 1 =
      ∑ j : Fin (n+1), R.coeff j.val / ((k+j.val+m+1 : ℕ) : K) := by
  have eq : X^m*R*X^k = X^(m+k)*R := by
    rw [pow_add]
    ac_rfl
  rw [eq]
  let T : K[X] →ₗ[K] K :=
    (Polynomial.leval 1).comp (primitive.comp (LinearMap.mulLeft K (X^(m+k) : K[X])))
  have h : T R = ∑ j ∈ Finset.range (n+1), R.coeff j / ((k+j+m+1 : ℕ) : K) := by
    conv_lhs => rw [R.as_sum_range' (n+1) (Nat.lt_succ_of_le degree), map_sum]
    apply Finset.sum_congr rfl
    intro j _
    change (primitive (X^(m+k)*monomial j (R.coeff j))).eval 1 = _
    rw [X_pow_mul_monomial, primitive_monomial, eval_monomial, one_pow, mul_one]
    rw [show j+(m+k)+1 = k+j+m+1 by omega]
  rw [← Fin.sum_univ_eq_sum_range] at h
  exact h

private theorem fin_cast_shift_sum (q : ℕ) (z : K) :
    ((∑ i : Fin q, (i.val : K)) + ∑ j : Fin q, ((j.val : K)+z)) =
      (q : K) * ((q : K)-1+z) := by
  induction q with
  | zero => simp
  | succ q ih =>
    simp only [Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last, Nat.cast_succ]
    calc
      _ = ((∑ i : Fin q, (i.val : K)) + ∑ j : Fin q, ((j.val : K)+z)) +
            (2*(q : K)+z) := by ring
      _ = _ := by rw [ih]; ring

/-- Exact endpoint strength already determined by the n+1 monomial tests.
The weight X^m and the normalization constant c are arbitrary. -/
theorem unit_X_power_monomial_tests_eval_one [CharZero K] {n : ℕ} (m : ℕ)
    (R : K[X]) (c : K) (degree : R.natDegree ≤ n)
    (fit : ∀ i : Fin (n+1), (primitive (X^m*R*X^i.val)).eval 1 = c) :
    R.eval 1 = c * (((n : K)+1) * ((n : K)+(m : K)+1)) := by
  let x (i : Fin (n+1)) : K := i.val
  let y (j : Fin (n+1)) : K := (j.val : K) + ((m : K)+1)
  let a (j : Fin (n+1)) : K := R.coeff j.val
  have xi : Function.Injective x := by
    intro i j h
    apply Fin.ext
    exact (Nat.cast_injective (R := K)) h
  have de (i j : Fin (n+1)) :
      x i + y j = ((i.val+j.val+m+1 : ℕ) : K) := by
    simp only [x, y, Nat.cast_add, Nat.cast_one]
    ring
  have nd (i j : Fin (n+1)) : x i+y j ≠ 0 := by
    rw [de i j]
    exact Nat.cast_ne_zero.mpr (by omega)
  have test (i : Fin (n+1)) : (∑ j : Fin (n+1), a j / (x i+y j)) = c := by
    have h := fit i
    rw [primitive_powerMoment_as_cauchy R degree m i.val] at h
    simpa only [a, de] using h
  have readout := cauchy_constant_solution_sum x y a c xi nd test
  have ev : R.eval 1 = ∑ j : Fin (n+1), a j := by
    change R.eval 1 = ∑ j : Fin (n+1), R.coeff j.val
    rw [eval_eq_sum_range' (Nat.lt_succ_of_le degree), Fin.sum_univ_eq_sum_range]
    simp only [one_pow, mul_one]
  have ct : ((∑ i : Fin (n+1), x i) + ∑ j : Fin (n+1), y j) =
      ((n : K)+1) * ((n : K)+(m : K)+1) := by
    change ((∑ i : Fin (n+1), (i.val : K)) +
      ∑ j : Fin (n+1), ((j.val : K)+((m : K)+1))) = _
    rw [fin_cast_shift_sum]
    simp only [Nat.cast_add, Nat.cast_one]
    ring
  exact ev.trans (readout.trans (congrArg (fun z : K => c*z) ct))

/-- Exact endpoint strength of any polynomial representing a scaled
evaluation functional in unit mass with the power weight X^m. -/
theorem unit_X_power_reproducer_eval_one [CharZero K] {n : ℕ} (m : ℕ)
    (R : K[X]) (c : K) (degree : R.natDegree ≤ n)
    (fit : ∀ H : K[X], H.natDegree ≤ n →
      (primitive (X^m*R*H)).eval 1 = c * H.eval 1) :
    R.eval 1 = c * (((n : K)+1) * ((n : K)+(m : K)+1)) := by
  apply unit_X_power_monomial_tests_eval_one m R c degree
  intro i
  have d : ((X : K[X])^i.val).natDegree ≤ n := by
    rw [natDegree_X_pow]
    exact Nat.le_of_lt_succ i.isLt
  simpa only [eval_pow, eval_X, one_pow, mul_one] using fit (X^i.val) d

/-- With degree at most q−1 (q=n+1), the unit X-weight endpoint
reproducer has the exact value q(q+1) at one. -/
theorem unit_X_reproducer_eval_one [CharZero K] {n : ℕ} (R : K[X])
    (degree : R.natDegree ≤ n)
    (fit : ∀ H : K[X], H.natDegree ≤ n →
      (primitive (X*R*H)).eval 1 = H.eval 1) :
    R.eval 1 = ((n : K)+1) * ((n : K)+2) := by
  have h (H : K[X]) (Hd : H.natDegree ≤ n) :
      (primitive (X^1*R*H)).eval 1 = (1 : K)*H.eval 1 := by
    simpa only [pow_one, one_mul] using fit H Hd
  have e := unit_X_power_reproducer_eval_one 1 R 1 degree h
  rw [one_mul, Nat.cast_one] at e
  calc
    R.eval 1 = ((n : K)+1) * ((n : K)+1+1) := e
    _ = _ := by ring

end
end RKResearch.Certified.Graded
