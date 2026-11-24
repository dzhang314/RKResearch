module
public import RKCert.PortGridSetup
public import RKCert.PortPrimitiveRows
public import RKCert.LobattoFactors

@[expose] public section
namespace RKCert.PortRank
open Polynomial Matrix RKCert.Paired RKCert.Paired.Terminal RKCert.FixedFactor
variable {K : Type*} [Field K] [CharZero K]

theorem full_grid_scale :
    ((X-1)*(lobatto (K:=K) 7)).scaleRoots (429:K)=
      C (24024:K)*(F.map (Int.castRingHom K)) := by
  have nz : lobatto (K:=K) 7≠0:=by
    intro e; have h:=degree_lobatto7 (K:=K); rw [e,natDegree_zero] at h; omega
  rw [show (X-1:K[X])=X-C 1 from by simp,mul_scaleRoots' _ _ _
    (mul_ne_zero (leadingCoeff_ne_zero.mpr (monic_X_sub_C _).ne_zero) (leadingCoeff_ne_zero.mpr nz)),
    X_sub_C_scaleRoots,one_mul,scaled_lobatto7]
  simp only [F,H,Polynomial.map_mul,Polynomial.map_sub,map_X,map_C,Int.coe_castRingHom,Int.cast_ofNat]
  ring

/-- Over any characteristic-zero field the four mixed global moments and
two local primitives exclude a nonzero quartic on every small factor of the
fixed eight-port Lobatto-7 grid. No positivity or nonzero-coefficient selection
under reduction is needed: only its determinant is specialized. -/
theorem lobatto7_quartic_of_det
    (cert : ∀(W:K[X]) (x:K), W.Monic→W∣F.map (Int.castRingHom K)→W.natDegree≤5→
      (H.map (Int.castRingHom K)).eval x=0→W.eval x=0→portDet W x≠0)
    (Z Q:K[X]) (u:K)
    (zm:Z.Monic) (zdiv:Z∣(X-1)*lobatto 7) (dz:Z.natDegree≤5)
    (hu:u≠0) (zu:Z.eval u=0) (dq:Q.natDegree≤4)
    (global : ∀k:Fin 4, (primitive ((X^k.val*Z)*Q)).eval 1=0)
    (local1 : (primitive (X*Q)).eval u=0) (local2 : (primitive (X^2*Q)).eval u=0) :
    Q=0 := by
  let W:=Z.scaleRoots (429:K)
  let x:K:=429*u
  have hx : x≠0:=mul_ne_zero (by norm_num) hu
  have wd : W∣F.map (Int.castRingHom K) := by
    have h:=zdiv.scaleRoots (r:=(429:K))
    rw [full_grid_scale] at h
    have un : IsUnit (C (24024:K)):=isUnit_C.mpr (isUnit_iff_ne_zero.mpr (by norm_num))
    exact un.dvd_mul_left.mp h
  have wz : W.eval x=0 := by dsimp only [W,x]; rw [scaleRoots_eval_mul,zu,mul_zero]
  have wh : (H.map (Int.castRingHom K)).eval x=0 := by
    obtain ⟨B,eq⟩:=wd
    have h : (F.map (Int.castRingHom K)).eval x=0 := by rw [eq,eval_mul,wz,zero_mul]
    rw [F,Polynomial.map_mul,map_X,eval_mul,eval_X] at h
    exact (mul_eq_zero.mp h).resolve_left hx
  have detN:=cert W x ((monic_scaleRoots_iff _).mpr zm) wd
    (by simpa only [W,natDegree_scaleRoots] using dz) wh wz
  have g (k:Fin 4) : (∑j:Fin 5,globalEntry W.coeff k.val j.val*scaledCoeff Q j)=0 := by
    dsimp only [W]
    rw [scaled_global_row _ (by have:=k.isLt; omega) _ _ dz dq,global,mul_zero]
  have l1 : (∑j:Fin 5,localEntry x 1 j.val*scaledCoeff Q j)=0 := by
    dsimp only [x]
    rw [scaled_local_row 1 (by decide) _ dq,pow_one,local1,mul_zero]
  have l2 : (∑j:Fin 5,localEntry x 2 j.val*scaledCoeff Q j)=0 := by
    dsimp only [x]
    rw [scaled_local_row 2 (by decide) _ dq,local2,mul_zero]
  have zero : portMatrix W.coeff x *ᵥ scaledCoeff Q=0 := by
    funext i
    fin_cases i
    · change (∑j:Fin 5,(globalEntry W.coeff 0 j.val-globalEntry W.coeff 1 j.val)*scaledCoeff Q j)=0
      simp only [sub_mul,Finset.sum_sub_distrib]
      exact sub_eq_zero.mpr ((g 0).trans (g 1).symm)
    · exact g 2
    · exact g 3
    · exact l1
    · exact l2
  by_contra qn
  let j:Fin 5:=⟨Q.natDegree,by omega⟩
  have jn : scaledCoeff Q j≠0 := mul_ne_zero (leadingCoeff_ne_zero.mpr qn) (pow_ne_zero _ (by norm_num))
  exact detN (Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors zero
    (mem_nonZeroDivisors_iff_ne_zero.mpr jn))


end RKCert.PortRank
