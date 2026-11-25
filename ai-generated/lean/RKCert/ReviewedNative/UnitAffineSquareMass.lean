module

public import RKCert.ReviewedNative.UnitBetaSquareMass
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.UnitAffineSquareMass

open Polynomial UnitBetaSquareMass
open scoped BigOperators Classical

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- A true affine polynomial with two nonnegative endpoint values, one positive. -/
structure EndpointAffine (L : K[X]) : Prop where
  degree : L.natDegree ≤ 1
  left_nonneg : 0 ≤ L.eval 0
  right_nonneg : 0 ≤ L.eval 1
  one_pos : 0 < L.eval 0 ∨ 0 < L.eval 1

theorem EndpointAffine.eq_endpoints {L : K[X]} (h : EndpointAffine L) :
    L = C (L.eval 0) * (1-X) + C (L.eval 1) * X := by
  have fit : L = C (L.coeff 1) * X + C (L.coeff 0) :=
    eq_X_add_C_of_natDegree_le_one h.degree
  have e0 : L.eval 0 = L.coeff 0 := by
    simpa only [eval_add, eval_C, eval_mul, eval_X, mul_zero, zero_add] using
      congrArg (Polynomial.eval (0 : K)) fit
  have e1 : L.eval 1 = L.coeff 1 + L.coeff 0 := by
    simpa only [eval_add, eval_C, eval_mul, eval_X, mul_one] using
      congrArg (Polynomial.eval (1 : K)) fit
  calc
    L = C (L.coeff 1) * X + C (L.coeff 0) := fit
    _ = _ := by rw [e0, e1, C_add]; ring

private theorem mass_split (a b : ℕ) {L : K[X]} (h : EndpointAffine L) (G : K[X]) :
    mass (betaWeight a b * L * G) =
      L.eval 0 * mass (betaWeight a (b+1) * G) +
        L.eval 1 * mass (betaWeight (a+1) b * G) := by
  have expand : betaWeight a b * L * G =
      C (L.eval 0) * (betaWeight a (b+1) * G) +
        C (L.eval 1) * (betaWeight (a+1) b * G) := by
    calc
      _ = betaWeight a b * (C (L.eval 0) * (1-X) + C (L.eval 1) * X) * G :=
        congrArg (fun Z => betaWeight a b * Z * G) h.eq_endpoints
      _ = _ := by simp only [betaWeight, pow_succ]; ring
  rw [expand]
  simp only [map_add, mass_C_mul]

/-- One affine factor preserves strict mass when the two shifted masses are positive. -/
theorem EndpointAffine.mass_mul_pos {L G : K[X]} (h : EndpointAffine L) (a b : ℕ)
    (left : 0 < mass (betaWeight a (b+1) * G))
    (right : 0 < mass (betaWeight (a+1) b * G)) :
    0 < mass (betaWeight a b * L * G) := by
  rw [mass_split a b h G]
  rcases h.one_pos with pos | pos
  · exact add_pos_of_pos_of_nonneg (mul_pos pos left) (mul_nonneg h.right_nonneg right.le)
  · exact add_pos_of_nonneg_of_pos (mul_nonneg h.left_nonneg left.le) (mul_pos pos right)

/-- Finite indexed product; equal polynomials at different indices are allowed. -/
theorem mass_beta_finset_prod_sq_pos {ι : Type*} (S : Finset ι) (L : ι → K[X])
    {P : K[X]} (Pn : P ≠ 0) :
    ∀ (a b : ℕ), (∀ i ∈ S, EndpointAffine (L i)) →
      0 < mass (betaWeight a b * (∏ i ∈ S, L i) * P^2) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      intro a b _
      simpa only [Finset.prod_empty, mul_one] using mass_beta_square_pos a b Pn
  | @insert i S off ih =>
      intro a b all
      have first : EndpointAffine (L i) := all i (Finset.mem_insert_self _ _)
      have rest : ∀ j ∈ S, EndpointAffine (L j) :=
        fun j hj => all j (Finset.mem_insert_of_mem hj)
      rw [Finset.prod_insert off]
      have re : betaWeight a b * (L i * (∏ j ∈ S, L j)) * P^2 =
          betaWeight a b * L i * ((∏ j ∈ S, L j) * P^2) := by ring
      rw [re]
      apply first.mass_mul_pos a b
      · simpa only [mul_assoc] using ih a (b+1) rest
      · simpa only [mul_assoc] using ih (a+1) b rest

/-- Literal list version, with the same repeated-factor semantics. -/
theorem mass_beta_list_prod_sq_pos (L : List K[X]) {P : K[X]} (Pn : P ≠ 0) :
    ∀ (a b : ℕ), (∀ f ∈ L, EndpointAffine f) →
      0 < mass (betaWeight a b * L.prod * P^2) := by
  induction L with
  | nil =>
      intro a b _
      simpa only [List.prod_nil, mul_one] using mass_beta_square_pos a b Pn
  | cons f L ih =>
      intro a b all
      have first : EndpointAffine f := all f (by simp)
      have rest : ∀ g ∈ L, EndpointAffine g :=
        fun g hg => all g (List.mem_cons.mpr (Or.inr hg))
      rw [List.prod_cons]
      have re : betaWeight a b * (f * L.prod) * P^2 =
          betaWeight a b * f * (L.prod * P^2) := by ring
      rw [re]
      apply first.mass_mul_pos a b
      · simpa only [mul_assoc] using ih a (b+1) rest
      · simpa only [mul_assoc] using ih (a+1) b rest

end
end RKCert.ReviewedNative.UnitAffineSquareMass
