module

public import RKCert.ReviewedNative.DIRK12F17CubicChecks
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace RKResearch.Certified.DIRK12F17Cubic

open RKResearch Graded FiniteRootedTree Polynomial
open scoped Matrix FiniteRootedTree

instance : Fact (Nat.Prime 17) := ⟨by decide +kernel⟩

section Generic

variable {R : Type*} [CommRing R] [CharP R 17] {z : R}

theorem small_unit (j : Nat) (h : j < 5) : IsUnit (((j+1 : Nat):R)) := by
  have hn : (((j+1 : Nat) : ZMod 17)) ≠ 0 := by
    intro hz
    have := (CharP.cast_eq_zero_iff (ZMod 17) 17 (j+1)).mp hz
    omega
  have e : IsUnit (((j+1 : Nat) : ZMod 17)) := isUnit_iff_ne_zero.mpr hn
  simpa only [map_natCast] using e.map (ZMod.castHom (dvd_refl 17) R)

theorem order_twelve (hz : IsCubic z) : HasOrder 12 (A z) (b z) :=
  DualSupport12.LowChecks.hasOrder (lowChecks hz receipts small_unit)

theorem next_defect_val (hz : IsCubic z) :
    val z nextDefect = (13 : R) * row (b z) ((nodes (A z))^12) - 1 := by
  unfold nextDefect
  rw [val_sub hz, val_mul hz, val_num, val_num, ev_dot hz, ev_X hz receipts, Nat.cast_one]
  rfl

def nextTree : FiniteRootedTree := bushyTree 13

theorem next_size : (nextTree.order : Nat) ≤ 13 := by decide +kernel

theorem unit_next_star (hz : IsCubic z) :
    IsUnit ((((nextTree.factorial : Nat) : R)) * (b z ⬝ᵥ Φ nextTree (A z)) - 1) := by
  have h := congrArg (val z) receipts.nextUnit
  rw [val_mul hz, val_num, Nat.cast_one] at h
  have unit := IsUnit.of_mul_eq_one (val z starInverse) h
  rw [next_defect_val hz] at unit
  have eq : ((nextTree.factorial : Nat) : R) = 13 := by
    rw [show (nextTree.factorial : Nat) = 13 by decide +kernel]
    rfl
  rw [eq, nextTree, Φ_bushyTree]
  exact unit

theorem next_value (hz : IsCubic z) :
    (13 : R)*row (b z) ((nodes (A z))^12) - 1 = 11+7*z+12*z^2 := by
  rw [← next_defect_val hz, receipts.witness]
  rfl

theorem distinct_diagonals [Nontrivial R] (hz : IsCubic z) :
    A z 0 0 ≠ A z 1 1 := by
  have e := congrArg (val z) receipts.diagUnit
  rw [val_mul hz, val_num, Nat.cast_one] at e
  have hu : IsUnit (val z (rawA 1 1)) := IsUnit.of_mul_eq_one (val z diagInverse) e
  change val z (rawA 0 0) ≠ val z (rawA 1 1)
  rw [receipts.firstDiag, val_num, Nat.cast_zero]
  exact hu.ne_zero.symm

theorem exact_of_cubic [Nontrivial R] (hz : IsCubic z) :
    Matrix.IsLowerTriangular (A z) ∧ A z 0 0 ≠ A z 1 1 ∧
      HasOrder 12 (A z) (b z) ∧ ¬ HasOrder 13 (A z) (b z) := by
  refine ⟨lower z, distinct_diagonals hz, order_twelve hz, ?_⟩
  intro h
  exact (unit_next_star hz).ne_zero (sub_eq_zero.mpr (h nextTree next_size))

end Generic

noncomputable def poly : (ZMod 17)[X] := X^3 + C 7 * X^2 + C 3 * X + C 10

theorem poly_degree : poly.natDegree = 3 := by
  unfold poly
  compute_degree <;> norm_num

theorem poly_monic : poly.Monic := by
  unfold poly
  monicity <;> norm_num

theorem poly_irred : Irreducible poly := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [poly_degree]
    decide
  · intro x
    have h : ∀ s : ZMod 17, s^3+7*s^2+3*s+10 ≠ 0 := by decide +kernel
    change ¬ poly.eval x = 0
    unfold poly
    simpa only [Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] using h x

instance : Fact (Irreducible poly) := ⟨poly_irred⟩

abbrev K := AdjoinRoot poly

instance : CharP K 17 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 17) K).injective 17

noncomputable def alpha : K := AdjoinRoot.root poly

theorem cubic_alpha : IsCubic alpha := by
  have h : alpha^3+7*alpha^2+3*alpha+10 = 0 := by
    have ea := AdjoinRoot.eval₂_root poly
    change (X^3 + C 7 * X^2 + C 3 * X + C 10 : (ZMod 17)[X]).eval₂ (AdjoinRoot.of poly) alpha = 0 at ea
    simpa only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C, Polynomial.eval₂_ofNat, Polynomial.eval₂_natCast, map_ofNat] using ea
  have e : (17:K) = 0 := CharP.cast_eq_zero K 17
  unfold IsCubic
  linear_combination h - (1+alpha+alpha^2)*e

theorem extension_degree : Module.finrank (ZMod 17) K = 3 := by
  exact (AdjoinRoot.powerBasis' poly_monic).finrank.trans poly_degree

theorem exact_f17_cubic :
    Matrix.IsLowerTriangular (A alpha) ∧ A alpha 0 0 ≠ A alpha 1 1 ∧
      HasOrder 12 (A alpha) (b alpha) ∧ ¬ HasOrder 13 (A alpha) (b alpha) :=
  exact_of_cubic cubic_alpha

end RKResearch.Certified.DIRK12F17Cubic

#print axioms RKResearch.Certified.DIRK12F17Cubic.order_twelve
#print axioms RKResearch.Certified.DIRK12F17Cubic.unit_next_star
#print axioms RKResearch.Certified.DIRK12F17Cubic.exact_f17_cubic
#print axioms RKResearch.Certified.DIRK12F17Cubic.extension_degree
