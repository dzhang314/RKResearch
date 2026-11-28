module

public import RKCert.ReviewedNative.GradedColumns
public import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Tactic.LinearCombination

@[expose] public section

/-! A direct next-order scalar gate for ten-site order-twelve quadrature.
Only the unoriented monic hull enters: no selected quadratic root or
number-field reduction occurs in the formula. -/
namespace RKResearch.Certified.DIRK12MidpointStar
open RKResearch Graded FiniteRootedTree Polynomial
open scoped Matrix BigOperators Polynomial FiniteRootedTree

section Scalar
variable {K : Type*} [Field K]

theorem monic_cancel {F H : K[X]} (hf : F.Monic) (hh : H.Monic)
    {n : Nat} (hn : 0 < n) (hF : F.natDegree = n) (hH : H.natDegree = n)
    (I Q : K[X] →ₗ[K] K)
    (low : ∀ P : K[X], P.natDegree < n → Q P = I P) (kills : Q H = 0) :
    Q F - I F = -I H := by
  have degreeSame : F.degree = H.degree := by
    rw [degree_eq_natDegree hf.ne_zero, degree_eq_natDegree hh.ne_zero, hF, hH]
  have strict : (F-H).natDegree < n := by
    by_cases hz : F-H=0
    · simpa [hz] using hn
    · apply (natDegree_lt_iff_degree_lt hz).mpr
      have h := degree_sub_lt_left degreeSame hf.ne_zero (hf.leadingCoeff.trans hh.leadingCoeff.symm)
      simpa only [degree_eq_natDegree hf.ne_zero, hF] using h
  have e := low (F-H) strict
  rw [map_sub, map_sub, kills] at e
  linear_combination e

variable {ι : Type*} [Fintype ι]

/-- Literal internal reflected nodes computed from the actual matrix. -/
def quadr (A : Matrix ι ι K) (b : ι → K) : K[X] →ₗ[K] K where
  toFun P := ∑ j, b j * P.eval (1-nodes A j)
  map_add' := by
    intro P Q
    simp only [eval_add,mul_add,Finset.sum_add_distrib]
  map_smul' := by
    intro r P
    simp only [RingHom.id_apply,Polynomial.eval_smul,smul_eq_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ac_rfl

theorem quadr_apply (A : Matrix ι ι K) (b : ι → K) (P : K[X]) :
    quadr A b P = ∑ j, b j * P.eval (1-nodes A j) := rfl

noncomputable def starPoly : K[X] := (X - C 1)^12

theorem quadr_star (A : Matrix ι ι K) (b : ι → K) :
    quadr A b starPoly = b ⬝ᵥ (nodes A)^12 := by
  rw [quadr_apply, dotProduct]
  simp only [starPoly, eval_pow, eval_sub, eval_X, eval_C, Pi.pow_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [show 1-nodes A i-1 = -nodes A i by ring]
  ring

/-- The first unpaid actual bush residual of a matched order-eleven scalar
quadrature is minus 13 times the integrated degree-twelve hull product. -/
theorem actual_star_defect (A : Matrix ι ι K) (b : ι → K) (S : K[X])
    (Smonic : S.Monic) (Sdegree : S.natDegree=10)
    (I : K[X] →ₗ[K] K) (exactScalar : ∀ P : K[X], P.natDegree<12 → quadr A b P = I P)
    (weightedRoots : ∀ i, b i * S.eval (1-nodes A i) = 0)
    (integralStar : 13 * I starPoly = 1) :
    (((bushyTree 13).factorial:Nat):K) * (b ⬝ᵥ Φ (bushyTree 13) A) - 1
      = -(13:K) * I (X^2*S) := by
  let F : K[X] := starPoly
  let H : K[X] := X^2*S
  have hf : F.Monic := (monic_X_sub_C (1:K)).pow 12
  have hh : H.Monic := ((monic_X : (X:K[X]).Monic).pow 2).mul Smonic
  have hF : F.natDegree=12 := by
    change ((X-C (1:K))^12).natDegree = 12
    rw [natDegree_pow, natDegree_X_sub_C, mul_one]
  have hH : H.natDegree=12 := by
    change ((X : K[X])^2*S).natDegree=12
    rw [natDegree_X_pow_mul 2 Smonic.ne_zero, Sdegree]
  have hroot : quadr A b H=0 := by
    rw [quadr_apply]
    apply Finset.sum_eq_zero
    intro i _
    simp only [H, eval_mul, eval_pow, eval_X]
    rw [mul_left_comm, weightedRoots i, mul_zero]
  have e := monic_cancel hf hh (by decide : 0<12) hF hH I (quadr A b) exactScalar hroot
  change quadr A b starPoly - I starPoly = -I (X^2*S) at e
  rw [quadr_star] at e
  rw [show ((bushyTree 13).factorial:Nat) = 13 by decide +kernel, Φ_bushyTree]
  change (13:K)*(b ⬝ᵥ (nodes A)^12)-1 = -(13:K)*I (X^2*S)
  linear_combination 13*e+integralStar

end Scalar
end RKResearch.Certified.DIRK12MidpointStar

#print axioms RKResearch.Certified.DIRK12MidpointStar.actual_star_defect
