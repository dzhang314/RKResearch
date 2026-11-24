module
public import RKCert.DirkSevenShape
public import RKCert.DirkLobattoQuadrature
@[expose] public section
namespace RKCert.SevenPort
open Matrix Polynomial RKCert.Paired RKCert.Paired.Terminal
variable {K:Type*} [Field K] [CharZero K]
noncomputable section
set_option maxRecDepth 3500
set_option maxHeartbeats 1500000
theorem clear_seven {n:ℕ} (lo:0<n)(hi:n≤17):((12252240/n:ℕ):K)=(12252240:K)/(n:K):=by
  have dv:n∣12252240:=by interval_cases n <;> decide
  apply (eq_div_iff (Nat.cast_ne_zero.mpr (Nat.ne_of_gt lo))).mpr
  exact_mod_cast Nat.div_mul_cancel dv
theorem entry_integral (t u:K)(n:ℕ)(hn:n≤9):
    entry t u n=12252240*integral (X^(n+1)*body t u):=by
  have one(k:ℕ):(X:K[X])^k=monomial k 1:=by rw [←C_mul_X_pow_eq_monomial,C_1,one_mul]
  rw [integral_eq,body,Finset.mul_sum]
  simp only [C_mul_X_pow_eq_monomial]
  simp only [one,monomial_mul_monomial,one_mul,map_sum,eval_finsetSum,
    primitive_monomial,eval_monomial,one_pow,mul_one,Finset.mul_sum]
  apply Finset.sum_congr rfl;intro i _
  have ie:=i.isLt
  rw [clear_seven (by omega:0<n+i.val+2) (by omega)]
  rw [show n+1+i.val+1=n+i.val+2 by omega]
  ring

theorem row_integral (t u:K)(T:K[X])(deg:T.natDegree≤4)(n:ℕ)(hn:n≤5):
    (∑j:Fin 5,entry t u (n+j.val)*T.coeff j.val)=12252240*integral (X^(n+1)*body t u*T):=by
  have sumT:T=∑j:Fin 5,T.coeff j.val • (X^j.val:K[X]):=by
    conv_lhs=>rw [T.as_sum_range' 5 (by omega),←Fin.sum_univ_eq_sum_range]
    simp only [smul_eq_C_mul,C_mul_X_pow_eq_monomial]
  conv_rhs=>rw [sumT,Finset.mul_sum]
  simp only [mul_smul_comm,map_sum,map_smul,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl;intro j _
  have e:X^(n+1)*body t u*X^j.val=X^(n+j.val+1)*body t u:=by
    rw [show n+j.val+1=(n+1)+j.val by omega,pow_add];ring
  rw [e,entry_integral t u _ (by have:=j.isLt;omega)];ring

theorem singular_minors (t u:K)(T:K[X])(deg:T.natDegree≤4)(nz:T≠0)
    (mom:∀k:Fin 6,integral (X^(k.val+1)*body t u*T)=0):
    d5 t u 0=0 ∧ d5 t u 1=0:=by
  have singular(k:ℕ)(hk:k≤1):d5 t u k=0:=by
    let c:Fin 5→K:=fun j=>T.coeff j.val
    have ker:matrix t u k *ᵥ c=0:=by
      funext i
      change (∑j:Fin 5,entry t u (k+i.val+j.val)*T.coeff j.val)=0
      have bound:k+i.val≤5:=by have:=i.isLt;omega
      rw [row_integral t u T deg _ bound,mom ⟨k+i.val,by omega⟩,mul_zero]
    let j:Fin 5:=⟨T.natDegree,by omega⟩
    exact Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors ker
      (i:=j) (mem_nonZeroDivisors_iff_ne_zero.mpr (show c j≠0 from leadingCoeff_ne_zero.mpr nz))
  exact ⟨singular 0 (by decide),singular 1 (by decide)⟩
end
end RKCert.SevenPort
