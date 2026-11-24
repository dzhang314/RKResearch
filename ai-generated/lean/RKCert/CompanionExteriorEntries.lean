module

public import RKCert.CompanionCoefficientMatrix
public import RKCert.CompanionPaidMoment

@[expose] public section

/-! # Exact ordered-subset compound entries for the companion moments -/
namespace RKCert.Compound
open Polynomial Module exteriorPower Set Set.powersetCard
open scoped Classical
noncomputable section

variable {K : Type*} [Field K]
variable {I : Type*} [Fintype I] [DecidableEq I] [LinearOrder I]
variable {V : Type*} [AddCommGroup V] [Module K V]

def orderedCompound (l : ℕ) (M : Matrix I I K) :
    Matrix (powersetCard I l) (powersetCard I l) K :=
  fun a b => (M.submatrix (powersetCard.ofFinEmbEquiv.symm a)
    (powersetCard.ofFinEmbEquiv.symm b)).det

theorem exterior_toMatrix_eq_compound (l : ℕ) (B : Basis I K V) (T : V→ₗ[K]V) :
    LinearMap.toMatrix (B.exteriorPower l) (B.exteriorPower l) (exteriorPower.map l T) =
      orderedCompound l (LinearMap.toMatrix B B T) := by
  ext a b
  rw [LinearMap.toMatrix_apply,exteriorPower.basis_apply]
  change (B.exteriorPower l).repr (exteriorPower.map l T
    (ιMulti K l (B ∘ powersetCard.ofFinEmbEquiv.symm b))) a=_
  rw [exteriorPower.map_apply_ιMulti,exteriorPower.basis_repr_apply,
    exteriorPower.ιMultiDual_apply_ιMulti]
  unfold orderedCompound
  rw [←Matrix.det_transpose]
  congr 1
  ext i j
  simp only [Matrix.transpose_apply,Matrix.of_apply,Function.comp_apply,Matrix.submatrix_apply,
    LinearMap.toMatrix_apply,Basis.coord_apply]

variable [CharZero K]

theorem factorMoment_toMatrix (q : K[X]) (hq : q.Monic) (k : ℕ) (u : K) (j : ℕ) :
    LinearMap.toMatrix ((AdjoinRoot.powerBasis' hq).basis.exteriorPower k)
      ((AdjoinRoot.powerBasis' hq).basis.exteriorPower k) (factorMomentOperator q k u j) =
    ∑ i : Fin (k+1),
      (paidMomentLinear u j (Lagrange.basis Finset.univ (factorSites K k) i)) •
          orderedCompound k (Matrix.scalar _ (factorSites K k i)-coefficientCompanion q) := by
  rw [factorMomentOperator,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul,exterior_toMatrix_eq_compound,shifted_root_matrix_entries]

end
end RKCert.Compound
