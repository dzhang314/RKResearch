module
public import RKCert.Dirk17RadauGrid
@[expose] public section
namespace RKCert.RadauEight
open Polynomial RKCert.Paired RKCert.Paired.Terminal RKCert.Endpoint RKCert.FixedFactor
variable {K:Type*} [Field K] [CharZero K]
noncomputable section
set_option maxHeartbeats 2000000

def density (K:Type*) [CommRing K]:K[X]:=(intHorner [9,-720,13860,-110880,450450,-1009008,1261260,-823680,218790]).map (Int.castRingHom K)

omit [CharZero K] in
theorem density_degree : (density K).natDegree≤8:=natDegree_map_le.trans (degree_horner_le _ 8 (by decide))

omit [CharZero K] in
theorem density_reversed (x:K):(density K).eval x=9*RKCert.Endpoint.rightWeight8 (1-x):=by
  norm_num [density,intHorner,RKCert.Endpoint.rightWeight8];ring

theorem density_moments (j:Fin 9):(formalPrimitive (X^j.val*density K)).eval 1=1:=by
  rw [primitive_eval_power_mul _ _ _ density_degree]
  fin_cases j <;> norm_num [Fin.sum_univ_succ,density,coeff_map,coeff_horner,readCoeff]

theorem grid_moments (j:Fin 8):integral (X^j.val*grid K)=0:=by
  rw [integral_eq,←formalPrimitive_eq_treePrimitive,primitive_eval_power_mul _ _ _ (grid_degree (K:=K)).le]
  fin_cases j <;> norm_num [Fin.sum_univ_succ,grid,raw,coeff_map,coeff_horner,readCoeff]

theorem grid_orthogonal (R:K[X]) (d:R.natDegree≤7):integral (grid K*R)=0:=by
  conv_lhs=>rw [R.as_sum_range' 8 (by omega)]
  rw [Finset.mul_sum,map_sum]
  apply Finset.sum_eq_zero
  intro j hj
  have small:=Finset.mem_range.mp hj
  have eqn:grid K*monomial j (R.coeff j)=(R.coeff j) • (X^j*grid K):=by
    rw [←C_mul_X_pow_eq_monomial,Polynomial.smul_eq_C_mul];ring
  rw [eqn,map_smul,grid_moments (⟨j,small⟩:Fin 8),smul_zero]

theorem cardinal_eval {u:K} {L:K[X]} (rep:(X-C u)*L=grid K) (Q:K[X]) (d:Q.natDegree≤8):
    integral (L*Q)=Q.eval u*integral L:=by
  obtain ⟨R,fac⟩:=dvd_iff_isRoot.mpr (show (Q-C (Q.eval u)).eval u=0 by simp)
  have form:Q=(X-C u)*R+C (Q.eval u):=sub_eq_iff_eq_add.mp fac
  have dr:R.natDegree≤7:=by
    by_cases rz:R=0
    · simp [rz]
    have h:=natDegree_sub_le Q (C (Q.eval u))
    rw [fac,natDegree_mul (X_sub_C_ne_zero _) rz,natDegree_X_sub_C] at h
    have lhs:(C (Q.eval u)).natDegree=0:=natDegree_C _
    omega
  have poly:L*Q=grid K*R+Q.eval u • L:=by rw [←rep,Polynomial.smul_eq_C_mul];linear_combination L*form
  rw [poly,map_add,grid_orthogonal R dr,map_smul,zero_add,smul_eq_mul]

theorem cardinal_nonzero {u:K} {L:K[X]} (rep:(X-C u)*L=grid K) (dL:L.natDegree≤8) (nz:L≠0):
    integral L≠0:=by
  intro bad
  apply nz
  apply primitive_shift_detect L (k:=0) dL 1 one_ne_zero
  intro i
  have test:=cardinal_eval rep (X^i.val) (by rw [natDegree_X_pow];have:=i.isLt;omega)
  rw [bad,mul_zero,mul_comm L,integral_eq,←formalPrimitive_eq_treePrimitive] at test
  simpa only [Nat.zero_add] using test
end
end RKCert.RadauEight
