module

public import RKCert.CompanionFactorLine

@[expose] public section

/-! # The exact standard companion entries for the semantic exterior gate

The column companion in the scalar arithmetic is the actual
multiplication-by-X matrix in the Mathlib monic AdjoinRoot power basis.
-/
namespace RKCert.Compound
open Polynomial Module
open scoped Classical
noncomputable section

variable {K : Type*} [Field K]

def coefficientCompanion (q : K[X]) : Matrix (Fin q.natDegree) (Fin q.natDegree) K :=
  fun i j => if j.val+1<q.natDegree then
    (if i.val=j.val+1 then 1 else 0)
  else -q.coeff i.val

set_option maxHeartbeats 1050000 in
theorem root_mul_matrix_eq_companion {q : K[X]} (hq : q.Monic) :
    Algebra.leftMulMatrix (AdjoinRoot.powerBasis' hq).basis (AdjoinRoot.root q) =
      coefficientCompanion q := by
  let B : Basis (Fin q.natDegree) K (AdjoinRoot q) := (AdjoinRoot.powerBasis' hq).basis
  change Algebra.leftMulMatrix B (AdjoinRoot.root q)=coefficientCompanion q
  ext i j
  rw [←Algebra.toMatrix_lmul_eq,LinearMap.toMatrix_apply]
  change B.repr (AdjoinRoot.root q*B j) i=coefficientCompanion q i j
  have power (k : Fin q.natDegree) : B k=(AdjoinRoot.root q)^k.val :=
    (AdjoinRoot.powerBasis' hq).basis_eq_pow k
  rw [power j,←pow_succ']
  by_cases step : j.val+1<q.natDegree
  · let x : Fin q.natDegree := ⟨j.val+1,step⟩
    have e : (AdjoinRoot.root q)^(j.val+1)=B x := (power x).symm
    rw [e,Basis.repr_self,Finsupp.single_apply]
    by_cases k : i.val=j.val+1
    · have e' : x=i := Fin.ext k.symm
      simp [coefficientCompanion,step,k,e']
    · have e' : x≠i := fun e => k (congrArg Fin.val e).symm
      simp [coefficientCompanion,step,k,e']
  · have e : j.val+1=q.natDegree := by have a:=j.isLt; omega
    have n0 : 0<q.natDegree := by have a:=j.isLt; omega
    rw [e,←AdjoinRoot.mk_X,←map_pow]
    change (AdjoinRoot.powerBasisAux' hq).repr (AdjoinRoot.mk q (X^q.natDegree)) i=_
    rw [AdjoinRoot.powerBasisAux'_repr_apply_to_fun,AdjoinRoot.modByMonicHom_mk]
    have small : (X^q.natDegree-q).natDegree≤q.natDegree-1 := by
      apply natDegree_le_iff_coeff_eq_zero.mpr
      intro k hk
      by_cases f : k=q.natDegree
      · rw [f,coeff_sub,coeff_X_pow,ite_eq_left rfl,coeff_natDegree,hq.leadingCoeff,sub_self]
      · rw [coeff_sub,coeff_X_pow,ite_eq_right f,
          coeff_eq_zero_of_natDegree_lt (by omega),sub_zero]
    have lt : (X^q.natDegree-q).degree<q.degree := by
      rw [degree_eq_natDegree hq.ne_zero]
      exact degree_le_natDegree.trans_lt (by exact_mod_cast (show (X^q.natDegree-q).natDegree<q.natDegree by omega))
    have d : (X^q.natDegree-(X^q.natDegree-q))=q := by abel
    have e0 := modByMonic_eq_of_dvd_sub hq
      (show q∣X^q.natDegree-(X^q.natDegree-q) by rw [d])
    rw [e0,(modByMonic_eq_self_iff hq).mpr lt,coeff_sub,coeff_X_pow]
    have ni : i.val≠q.natDegree := by have z:=i.isLt; omega
    simp [coefficientCompanion,step,ni]

theorem shifted_root_matrix_entries {q : K[X]} (hq : q.Monic) (u : K) :
    LinearMap.toMatrix (AdjoinRoot.powerBasis' hq).basis (AdjoinRoot.powerBasis' hq).basis
      (shiftedRootOperator q u) = Matrix.scalar _ u-coefficientCompanion q := by
  change LinearMap.toMatrix (AdjoinRoot.powerBasis' hq).basis (AdjoinRoot.powerBasis' hq).basis
    (LinearMap.mulLeft K (algebraMap K (AdjoinRoot q) u-AdjoinRoot.root q))=_
  rw [Algebra.toMatrix_lmul_eq,map_sub,AlgHom.commutes,root_mul_matrix_eq_companion]
  rfl

end
end RKCert.Compound
