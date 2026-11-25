module

public import RKCert.ReviewedNative.DiagonalTreeShift
public import RKCert.ReviewedNative.GradedColumns
public import Mathlib.Algebra.Algebra.Bilinear

@[expose] public section

/-! The recursive shift agrees with literal matrix diagonal translation.
No support, ordering of stages, or division is required. -/
namespace RKResearch.DiagonalTreeShift

open RKResearch FiniteRootedTree RKResearch.Certified.Graded
open scoped FiniteRootedTree Matrix

noncomputable section

variable {ι R : Type*} [Fintype ι] [CommSemiring R]

def stageLift (A : Matrix ι ι R) : TreeCombination R →ₗ[R] (ι → R) :=
  lift R (fun t => Φ t A)

@[simp] theorem stageLift_atom (A : Matrix ι ι R) (t : FiniteRootedTree) :
    stageLift A (atom R t) = Φ t A := lift_atom R _ t

theorem stageLift_join (A : Matrix ι ι R) (x y : TreeCombination R) :
    stageLift A (join R x y) = stageLift A x * stageLift A y := by
  change stageLift A (join R x y) = LinearMap.mul R (ι → R) (stageLift A x) (stageLift A y)
  apply lift_join_of_atoms R
  intro t u
  simp only [stageLift_atom, Φ_rootedSum, LinearMap.mul_apply']

theorem stageLift_unary (A : Matrix ι ι R) (x : TreeCombination R) :
    stageLift A (unary R x) = mat A (stageLift A x) := by
  change ((stageLift A).comp (unary R)) x = ((mat A).comp (stageLift A)) x
  apply LinearMap.congr_fun
  apply hom_ext_atoms R
  intro t
  simp only [LinearMap.comp_apply, unary_atom, stageLift_atom, Φ, one_mul, mat_apply]

variable [DecidableEq ι]

theorem stageLift_expand (A : Matrix ι ι R) (a : R) (t : FiniteRootedTree) :
    stageLift A (expand R a t) = Φ t (A + a • (1 : Matrix ι ι R)) := by
  have act (v : ι → R) :
      ((A + a • (1 : Matrix ι ι R)) *ᵥ v) = mat A v + a • v := by
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, mat_apply]
  induction t with
  | leaf => simp only [expand, stageLift_atom, Φ]
  | butcherProduct t u ht hu =>
    simp only [expand, stageLift_join, map_add, map_smul, stageLift_unary, ht, hu, Φ, act]
    rw [mul_add, Algebra.mul_smul_comm]

theorem transform_tableau_output (A : Matrix ι ι R) (b : ι → R)
    (a : R) (t : FiniteRootedTree) :
    transform R a (fun u => b ⬝ᵥ Φ u A) t =
      b ⬝ᵥ Φ t (A + a • (1 : Matrix ι ι R)) := by
  have read : lift R (fun u => b ⬝ᵥ Φ u A) = (row b).comp (stageLift A) := by
    apply hom_ext_atoms R
    intro u
    simp only [lift_atom, LinearMap.comp_apply, stageLift_atom, row_apply]
  rw [transform, read, LinearMap.comp_apply, stageLift_expand, row_apply]

end
end RKResearch.DiagonalTreeShift
