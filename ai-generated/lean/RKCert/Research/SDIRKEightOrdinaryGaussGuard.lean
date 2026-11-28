import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

namespace RKResearch.Certified

variable {R : Type*} [CommRing R] [IsDomain R] {n : ℕ}

/-- A Vandermonde moment null vector on n+1 distinct sites, paid through
degree n-1, is either identically zero or has no zero coordinate. -/
theorem fullSupport_of_vanishing_moments
    {x q : Fin (n+1) → R} (hx : Function.Injective x)
    (hm : ∀ j : Fin n, (∑ i : Fin (n+1), q i * x i ^ (j : ℕ)) = 0)
    (hn : q ≠ 0) (k : Fin (n+1)) : q k ≠ 0 := by
  intro hk
  have hv : (fun i : Fin n => q (k.succAbove i)) = 0 := by
    apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero
      (f := x ∘ k.succAbove) (hx.comp Fin.succAbove_right_injective)
    intro j
    have h := hm j
    rw [Fin.sum_univ_succAbove _ k, hk, zero_mul, zero_add] at h
    exact h
  apply hn
  funext i
  by_cases h : i = k
  · simpa [h] using hk
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq h
    exact congrFun hv j

/-- A nonzero degree-at-most-n polynomial orthogonal to the first n
monomials of an (n+1)-site weighted rule cannot vanish at a live site. -/
theorem eval_ne_zero_on_live_sites_of_orthogonal
    {x w : Fin (n+1) → R} (hx : Function.Injective x) (hw : ∀ i, w i ≠ 0)
    {P : Polynomial R} (hP : P ≠ 0) (hdeg : P.natDegree ≤ n)
    (hm : ∀ j : Fin n, (∑ i : Fin (n+1), (w i * P.eval (x i)) * x i ^ (j : ℕ)) = 0)
    (k : Fin (n+1)) : P.eval (x k) ≠ 0 := by
  let q := fun i => w i * P.eval (x i)
  have hq : q ≠ 0 := by
    intro h
    apply hP
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero P hx
    · intro i
      exact (mul_eq_zero.mp (congrFun h i)).resolve_left (hw i)
    · simpa using Nat.lt_succ_of_le hdeg
  intro h
  exact fullSupport_of_vanishing_moments hx hm hq k (by simp [h])


open Polynomial in
/-- The shifted degree-four Legendre polynomial on the unit interval. -/
noncomputable def gaussFour (R : Type*) [CommRing R] : Polynomial R :=
  C 70*X^4-C 140*X^3+C 90*X^2-C 20*X+1

open Polynomial in
/-- An ordinary order-eight scalar rule on exactly five distinct live clocks
does not contain a degree-four Gaussian clock. The moments are denominator-free. -/
theorem gaussFour_ne_zero_of_five_live_moments
    {x w : Fin 5 → R} (hx : Function.Injective x) (hw : ∀ i, w i ≠ 0)
    (hM : ∀ j : ℕ, j < 8 → ((j+1 : ℕ) : R) * (∑ i : Fin 5, w i * x i ^ j) = 1)
    (k : Fin 5) : (gaussFour R).eval (x k) ≠ 0 := by
  let m := fun j : ℕ => ∑ i : Fin 5, w i * x i ^ j
  have hr (j : ℕ) (hj : j < 8) : ((j+1 : ℕ) : R) * m j = 1 := hM j hj
  have nz (j : ℕ) (hj : j < 8) : ((j+1 : ℕ) : R) ≠ 0 := by
    intro hz
    have h := hr j hj
    rw [hz,zero_mul] at h
    exact zero_ne_one h
  have h840 : (840:R) ≠ 0 := by
    rw [show (840:R) = (8:R)*3*5*7 by norm_num]
    have h8 : (8:R) ≠ 0 := by simpa using nz 7 (by decide)
    have h3 : (3:R) ≠ 0 := by simpa using nz 2 (by decide)
    have h5 : (5:R) ≠ 0 := by simpa using nz 4 (by decide)
    have h7 : (7:R) ≠ 0 := by simpa using nz 6 (by decide)
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero h8 h3) h5) h7
  have hpoly : gaussFour R ≠ 0 := by
    intro hz
    have h : (gaussFour R).eval 0 = (1:R) := by simp [gaussFour]
    rw [hz, eval_zero] at h
    exact zero_ne_one h
  have hdeg : (gaussFour R).natDegree ≤ 4 := by unfold gaussFour; compute_degree
  apply eval_ne_zero_on_live_sites_of_orthogonal hx hw hpoly hdeg _ k
  intro j
  let v := (j : ℕ)
  have hpoint (i : Fin 5) :
      (w i * (gaussFour R).eval (x i)) * x i ^ v =
        70*(w i*x i^(v+4))-140*(w i*x i^(v+3))+90*(w i*x i^(v+2))-
          20*(w i*x i^(v+1))+w i*x i^v := by
    simp only [gaussFour,eval_add,eval_sub,eval_mul,eval_pow,eval_C,eval_X,eval_one,pow_add]
    ring
  change (∑ i : Fin 5, (w i * (gaussFour R).eval (x i)) * x i ^ v) = 0
  simp only [hpoint, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [← Finset.mul_sum]
  change 70*m (v+4)-140*m (v+3)+90*m (v+2)-20*m (v+1)+m v = 0
  apply (mul_eq_zero.mp ?_).resolve_left h840
  dsimp [v]
  fin_cases j
  · change (840:R)*(70*m 4-140*m 3+90*m 2-20*m 1+m 0) = 0
    linear_combination 840 * hr 0 (by decide) - 8400 * hr 1 (by decide) + 25200 * hr 2 (by decide) - 29400 * hr 3 (by decide) + 11760 * hr 4 (by decide)
  · change (840:R)*(70*m 5-140*m 4+90*m 3-20*m 2+m 1) = 0
    linear_combination 420 * hr 1 (by decide) - 5600 * hr 2 (by decide) + 18900 * hr 3 (by decide) - 23520 * hr 4 (by decide) + 9800 * hr 5 (by decide)
  · change (840:R)*(70*m 6-140*m 5+90*m 4-20*m 3+m 2) = 0
    linear_combination 280 * hr 2 (by decide) - 4200 * hr 3 (by decide) + 15120 * hr 4 (by decide) - 19600 * hr 5 (by decide) + 8400 * hr 6 (by decide)
  · change (840:R)*(70*m 7-140*m 6+90*m 5-20*m 4+m 3) = 0
    linear_combination 210 * hr 3 (by decide) - 3360 * hr 4 (by decide) + 12600 * hr 5 (by decide) - 16800 * hr 6 (by decide) + 7350 * hr 7 (by decide)

#print axioms gaussFour_ne_zero_of_five_live_moments

#print axioms fullSupport_of_vanishing_moments
#print axioms eval_ne_zero_on_live_sites_of_orthogonal
end RKResearch.Certified
