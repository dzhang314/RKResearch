module

public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Algebra.Polynomial.Eval.SMul
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Finite signed nodal laws and augmented Gaussian exactness

Draft. Algebra only: the incoming weights may have either sign. Positivity
and order of the augmented rule are separate consumers, not hypotheses of
the division-and-Lagrange construction.
-/
namespace RKCert.ReviewedNative.FiniteGaussianNodalLift

open Polynomial
open scoped BigOperators

noncomputable section
variable {K : Type*} [Field K]

/-- Exactness through the stated degree, with no weight sign assumption. -/
def ExactRule {ι : Type*} (J : K[X] →ₗ[K] K) (s : Finset ι)
    (v : ι → K) (μ : ι → K) (d : ℕ) : Prop :=
  ∀ P : K[X], P.natDegree ≤ d → J P = ∑ i ∈ s, μ i * P.eval (v i)

/-- Inserting a common polynomial factor in a linear moment functional. -/
def weighted (J : K[X] →ₗ[K] K) (H : K[X]) : K[X] →ₗ[K] K :=
  J.comp (LinearMap.mulLeft K H)

@[simp] theorem weighted_apply (J : K[X] →ₗ[K] K) (H P : K[X]) :
    weighted J H P = J (H*P) := rfl

/-- Canonical masses for a prescribed finite set of distinct marks. -/
def cardinalMass {ι : Type*} [DecidableEq ι] (J : K[X] →ₗ[K] K)
    (s : Finset ι) (v : ι → K) (i : ι) : K :=
  J (Lagrange.basis s v i)

/-- Multiplying a paid test by the signed support polynomial kills every
atom. The total tested degree is explicitly charged. -/
theorem signed_nodal_annihilation {ι : Type*} {s : Finset ι} {f : ι → K}
    {μ : ι → K} {J : K[X] →ₗ[K] K} {D b : ℕ}
    (law : ExactRule J s f μ D)
    (cost : s.card+b ≤ D) (Q : K[X]) (degQ : Q.natDegree ≤ b) :
    J (Lagrange.nodal s f * Q) = 0 := by
  have deg : (Lagrange.nodal s f * Q).natDegree ≤ D := by
    exact (natDegree_mul_le_of_le
      (le_of_eq (Lagrange.natDegree_nodal (s := s) (v := f))) degQ).trans cost
  rw [law _ deg]
  apply Finset.sum_eq_zero
  intro i hi
  simp only [eval_mul,Lagrange.eval_nodal_at_node hi,zero_mul,mul_zero]

/-- If a marked nodal polynomial factors into the inserted weight and the
signed support polynomial, the same paid tests give its orthogonality. -/
theorem marked_nodal_annihilation {ι η : Type*} {s : Finset ι} {t : Finset η}
    {f : ι → K} {v : η → K} {μ : ι → K} {J : K[X] →ₗ[K] K}
    {H : K[X]} {D b : ℕ}
    (law : ExactRule (weighted J H) s f μ D)
    (factor : Lagrange.nodal t v = H * Lagrange.nodal s f)
    (cost : s.card+b ≤ D) (Q : K[X]) (degQ : Q.natDegree ≤ b) :
    J (Lagrange.nodal t v * Q) = 0 := by
  rw [factor,mul_assoc]
  exact signed_nodal_annihilation law cost Q degQ

/-- Nodal orthogonality through degree n−1 gives degree 2n−1 exactness on
the same n nodes. The quotient is killed by orthogonality, and only the
remainder uses interpolation. -/
theorem gaussian_exact_of_annihilates {ι : Type*} [DecidableEq ι]
    (J : K[X] →ₗ[K] K) (t : Finset ι) (v : ι → K)
    (nodes : Set.InjOn v t)
    (annihilate : ∀ Q : K[X], Q.natDegree ≤ t.card-1 →
      J (Lagrange.nodal t v*Q) = 0) :
    ExactRule J t v (cardinalMass J t v) (2*t.card-1) := by
  intro P pd
  let M : K[X] := Lagrange.nodal t v
  let Q := P /ₘ M
  let L := P %ₘ M
  have monic : M.Monic := Lagrange.nodal_monic (s := t) (v := v)
  have md : M.natDegree = t.card := Lagrange.natDegree_nodal
  have qd : Q.natDegree ≤ t.card-1 := by
    change (P /ₘ M).natDegree ≤ t.card-1
    rw [natDegree_divByMonic P monic,md]
    omega
  have ld : L.degree < (t.card : WithBot ℕ) := by
    have h := degree_modByMonic_lt P monic
    simpa only [M,L,Lagrange.degree_nodal] using h
  have decomp : L + M*Q = P := modByMonic_add_div P M
  have eval_eq (i : ι) (hi : i ∈ t) : L.eval (v i) = P.eval (v i) := by
    have h := congrArg (Polynomial.eval (v i)) decomp
    have hm : M.eval (v i) = 0 := Lagrange.eval_nodal_at_node hi
    simpa only [eval_add,eval_mul,hm,zero_mul,add_zero] using h
  have hJ : J P = J L := by
    have h := congrArg (fun S : K[X] => J S) decomp
    change J (L + Lagrange.nodal t v*Q) = J P at h
    rw [map_add,annihilate Q qd,add_zero] at h
    exact h.symm
  have hL := Lagrange.eq_interpolate nodes ld
  rw [hJ,hL,Lagrange.interpolate_apply,map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Polynomial.smul_eq_C_mul,map_smul,smul_eq_mul,eval_eq i hi]
  exact mul_comm _ _

/-- Signed exactness with a marked factor gives an exact augmented rule.
The increase in degree equals the increase in the number of marks when
the input is charged at the displayed minimal cutoff. -/
theorem gaussian_exact_of_signed_marks {ι η : Type*} [DecidableEq η]
    {s : Finset ι} {t : Finset η} {f : ι → K} {v : η → K}
    {μ : ι → K} {J : K[X] →ₗ[K] K} {H : K[X]} {D : ℕ}
    (law : ExactRule (weighted J H) s f μ D)
    (nodes : Set.InjOn v t)
    (factor : Lagrange.nodal t v = H*Lagrange.nodal s f)
    (cost : s.card+(t.card-1) ≤ D) :
    ExactRule J t v (cardinalMass J t v) (2*t.card-1) :=
  gaussian_exact_of_annihilates J t v nodes
    (marked_nodal_annihilation law factor cost)

/-- Two extra distinct marks raise the exactness degree by two. At four
old marks these are precisely the cutoffs 9 and 11. -/
theorem gaussian_exact_of_two_marks {ι η : Type*} [DecidableEq η]
    {s : Finset ι} {t : Finset η} {f : ι → K} {v : η → K}
    {μ : ι → K} {J : K[X] →ₗ[K] K} {H : K[X]}
    (law : ExactRule (weighted J H) s f μ (2*s.card+1))
    (nodes : Set.InjOn v t) (count : t.card = s.card+2)
    (factor : Lagrange.nodal t v = H*Lagrange.nodal s f) :
    ExactRule J t v (cardinalMass J t v) (2*s.card+3) := by
  have h := gaussian_exact_of_signed_marks law nodes factor (by omega)
  have hc : 2*t.card-1 = 2*s.card+3 := by omega
  simpa only [hc] using h

/-- Hence the nodal masses can be computed on the squares of the cardinal
polynomials, even if the construction initially had no sign information. -/
theorem mass_eq_cardinal_square {ι : Type*} [DecidableEq ι]
    {J : K[X] →ₗ[K] K} {t : Finset ι} {v : ι → K} {μ : ι → K}
    (nodes : Set.InjOn v t)
    (law : ExactRule J t v μ (2*t.card-1)) {i : ι} (hi : i ∈ t) :
    μ i = J ((Lagrange.basis t v i)^2) := by
  let P := Lagrange.basis t v i
  have deg : (P^2).natDegree ≤ 2*t.card-1 := by
    have hp : P.natDegree ≤ t.card-1 := le_of_eq (Lagrange.natDegree_basis nodes hi)
    exact (natDegree_pow_le_of_le 2 hp).trans (by omega)
  change μ i = J (P^2)
  rw [law _ deg]
  symm
  calc
    (∑ j ∈ t, μ j*(P^2).eval (v j)) = μ i*(P^2).eval (v i) := by
      apply Finset.sum_eq_single i
      · intro j hj hji
        have hz : P.eval (v j) = 0 := Lagrange.eval_basis_of_ne hji.symm hj
        simp [eval_pow,hz]
      · intro hm
        exact (hm hi).elim
    _ = μ i := by
      have ho : P.eval (v i) = 1 := Lagrange.eval_basis_self nodes hi
      simp [eval_pow,ho]

theorem nodal_insert_two {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (v : ι → K) {i j : ι}
    (hj : j ∉ s) (hi : i ∉ insert j s) :
    Lagrange.nodal (insert i (insert j s)) v =
      ((X-C (v i))*(X-C (v j)))*Lagrange.nodal s v := by
  rw [Lagrange.nodal_insert_eq_nodal hi,Lagrange.nodal_insert_eq_nodal hj]
  exact (mul_assoc _ _ _).symm

end
end RKCert.ReviewedNative.FiniteGaussianNodalLift
