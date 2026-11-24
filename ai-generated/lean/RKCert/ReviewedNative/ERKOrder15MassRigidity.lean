module

public import RKCert.ReviewedNative.JacobiEndpointMass
import RKCert.ReviewedNative.JacobiMomentBand
import Mathlib.Tactic.LinearCombination

@[expose] public section

/-! # Two paid shifts and the true terminal mass kill the polynomial correction

Only adjacent moments, one scalar shift relation, and two exact endpoint
masses are used. The generic Jacobi theorem replaces tabulated ghosts. -/
namespace RKCert.ReviewedNative.JacobiMoments

open Polynomial RKCert.Endpoint
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

/-- Unit moment less the atom of mass rho at one. -/
def atomResidual (rho : K) : K[X] →ₗ[K] K :=
  (Polynomial.leval 1).comp formalPrimitiveLinear-rho • Polynomial.leval 1

@[simp] theorem atomResidual_apply (rho : K) (P : K[X]) :
    atomResidual rho P = (formalPrimitive P).eval 1-rho*P.eval 1 := rfl

private theorem atom_mesh (rho : K) (m : ℕ) (hm : 0<m) :
    atomResidual rho (X*signedSlope K m)=1-rho*((m:K)*((m:K)+1)) := by
  rw [atomResidual_apply,formalPrimitive_x_signedSlope_at_one (K:=K) m hm,eval_mul,eval_X,
    one_mul,signedSlope_at_one]

private theorem adjacent_two_meshes {m : ℕ} (hm : 3≤m) (P : K[X]) (pd : P.natDegree≤m+1)
    (p0 : P.coeff 0=0)
    (obs : ∀ k≤m-2,(formalPrimitive (X^k*P)).eval 1=(formalPrimitive (X^(k+1)*P)).eval 1) :
    ∃ c d : K, P=C c*(X*signedSlope K (m+1))+C d*(X*signedSlope K m) := by
  obtain ⟨D,e⟩ := Polynomial.X_dvd_iff.mpr p0
  have dd : D.natDegree≤m := by
    by_cases z : D=0
    · simp [z]
    · rw [e,natDegree_X_mul z] at pd
      omega
  have mom : MomentDifferences D (m-2) := by
    intro k
    rw [←e]
    exact obs k.val (by have := k.isLt;omega)
  obtain ⟨c,d,h⟩ := signedSlope_band (r:=m-2) (by omega : D.natDegree≤m-2+2) mom
  rw [show m-2+3=m+1 by omega,show m-2+2=m by omega] at h
  refine ⟨c,d,?_⟩
  rw [e,h]
  ring

private theorem adjacent_one_mesh {m : ℕ} (hm : 3≤m) (P : K[X]) (pd : P.natDegree≤m)
    (p0 : P.coeff 0=0)
    (obs : ∀ k≤m-2,(formalPrimitive (X^k*P)).eval 1=(formalPrimitive (X^(k+1)*P)).eval 1) :
    ∃ d : K, P=C d*(X*signedSlope K m) := by
  obtain ⟨c,d,e⟩ := adjacent_two_meshes hm P (by omega) p0 obs
  have cz : c=0 := by
    by_contra cn
    have hi : (C c*(X*signedSlope K (m+1))).natDegree=m+1 := by
      rw [natDegree_C_mul cn,x_signedSlope_degree _ (by omega)]
    have lo : (C d*(X*signedSlope K m)).natDegree≤m :=
      (natDegree_C_mul_le ..).trans (x_signedSlope_degree m (by omega)).le
    have lt : (C d*(X*signedSlope K m)).natDegree < (C c*(X*signedSlope K (m+1))).natDegree := by
      rw [hi];omega
    have bad := natDegree_add_eq_left_of_natDegree_lt lt
    rw [←e,hi] at bad
    omega
  exact ⟨d,by simpa only [cz,map_zero,zero_mul,zero_add] using e⟩

private theorem nonzero_mass_of_line {m : ℕ} {P : K[X]} {rho : K} (hm : 0<m)
    (Pn : P≠0) (line : ∃ c : K,P=C c*(X*signedSlope K m))
    (mass : atomResidual rho P=0) : 1-rho*((m:K)*((m:K)+1))=0 := by
  obtain ⟨c,e⟩ := line
  have cn : c≠0 := fun z => Pn (by rw [e,z,map_zero,zero_mul])
  rw [e,←smul_eq_C_mul,map_smul,smul_eq_mul,atom_mesh rho m hm] at mass
  exact (mul_eq_zero.mp mass).resolve_left cn

/-- The genuine terminal contrast eliminates the missing last probe
without constructing an extra shift or using a hard-coded basis. -/
theorem two_shift_terminal_rigid {a : ℕ} {P Q G : K[X]} {rho t : K}
    (alo : 6≤a) (ahi : a≤7)
    (pd : P.natDegree≤a) (qd : Q.natDegree≤a) (p0 : P.coeff 0=0)
    (gd : G.natDegree=a+1) (g0 : G.coeff 0=0)
    (obs : ∀ k≤a-2,(formalPrimitive (X^k*P)).eval 1=(formalPrimitive (X^(k+1)*P)).eval 1)
    (gobs : ∀ k≤5,(formalPrimitive (X^k*G)).eval 1=(formalPrimitive (X^(k+1)*G)).eval 1)
    (pm : (formalPrimitive P).eval 1=rho*P.eval 1)
    (qm : (formalPrimitive Q).eval 1=rho*Q.eval 1)
    (shift : X*P-Q=C t*G) : P=0 := by
  by_contra pn
  have ln := adjacent_one_mesh (by omega : 3≤a) P pd p0 obs
  have pe : P.natDegree=a := by
    obtain ⟨c,e⟩ := ln
    have cn : c≠0 := fun z => pn (by rw [e,z,map_zero,zero_mul])
    rw [e,natDegree_C_mul cn,x_signedSlope_degree _ (by omega)]
  have a1 := nonzero_mass_of_line (rho:=rho) (by omega) pn ln (sub_eq_zero.mpr pm)
  have tn : t≠0 := by
    intro z
    have eq : X*P=Q := sub_eq_zero.mp (by simpa [z] using shift)
    rw [←eq,natDegree_X_mul pn,pe] at qd
    omega
  have pxm : atomResidual rho (X*P)=0 := by
    have h0 : (formalPrimitive P).eval 1=(formalPrimitive (X*P)).eval 1 := by
      simpa only [pow_zero,zero_add,pow_one,one_mul] using obs 0 (by omega)
    rw [atomResidual_apply,←h0,pm,eval_mul,eval_X,one_mul,sub_self]
  have gg := congrArg (atomResidual rho) shift
  rw [map_sub,pxm,show atomResidual rho Q=0 by exact sub_eq_zero.mpr qm,sub_zero,
    ←smul_eq_C_mul,map_smul,smul_eq_mul] at gg
  have gm : atomResidual rho G=0 := (mul_eq_zero.mp gg.symm).resolve_left tn
  have gn : G≠0 := fun h => by rw [h,natDegree_zero] at gd;omega
  have a2 : 1-rho*(((a:K)+1)*((a:K)+2))=0 := by
    by_cases az : a=6
    · have bg := adjacent_one_mesh (m:=a+1) (by omega) G gd.le g0
        (fun k hk => gobs k (by omega))
      have v := nonzero_mass_of_line (rho:=rho) (by omega) gn bg gm
      push_cast at v
      linear_combination v
    · have az7 : a=7 := by omega
      obtain ⟨c,d,e⟩ := adjacent_two_meshes (m:=a) (by omega) G gd.le g0
        (fun k hk => gobs k (by omega))
      have cn : c≠0 := by
        intro z
        rw [e,z,map_zero,zero_mul,zero_add] at gd
        have ub : (C d*(X*signedSlope K a)).natDegree≤a :=
          (natDegree_C_mul_le ..).trans (x_signedSlope_degree a (by omega)).le
        omega
      rw [e,map_add,←smul_eq_C_mul,←smul_eq_C_mul,map_smul,map_smul,smul_eq_mul,smul_eq_mul,
        atom_mesh rho (a+1) (by omega),atom_mesh rho a (by omega),a1,mul_zero,add_zero] at gm
      have v := (mul_eq_zero.mp gm).resolve_left cn
      push_cast at v
      linear_combination v
  have hh : (2:K)=0 := by linear_combination ((a:K)+2)*a1-(a:K)*a2
  exact two_ne_zero hh

end
end RKCert.ReviewedNative.JacobiMoments
