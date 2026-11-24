module
public import RKCert.PortMomentMatrix
public import RKCert.FactorPrimitiveScale

@[expose] public section
namespace RKCert.PortRank
open Polynomial Matrix RKCert.Paired
variable {K : Type*} [Field K]

theorem monomial_Xpow (k:ℕ) : (X:K[X])^k=monomial k 1 := by
  rw [←C_mul_X_pow_eq_monomial,C_1,one_mul]

theorem primitive_global_sum (k:ℕ) (Z Q:K[X]) (dZ:Z.natDegree≤5) (dQ:Q.natDegree≤4) :
    (primitive ((X^k*Z)*Q)).eval 1 =
    ∑j∈Finset.range 5, ∑i∈Finset.range 6,
        Z.coeff i*Q.coeff j/((k+i+j+1:ℕ):K) := by
  conv_lhs => rw [Z.as_sum_range' 6 (by omega),Q.as_sum_range' 5 (by omega),monomial_Xpow]
  simp only [Finset.mul_sum,Finset.sum_mul,monomial_mul_monomial,one_mul,map_sum,eval_finsetSum,
    primitive_monomial,eval_monomial,one_pow,mul_one]

theorem primitive_local_sum (k:ℕ) (Q:K[X]) (dQ:Q.natDegree≤4) (u:K) :
    (primitive (X^k*Q)).eval u = ∑j∈Finset.range 5, Q.coeff j/((k+j+1:ℕ):K)*u^(k+j+1) := by
  conv_lhs => rw [Q.as_sum_range' 5 (by omega),monomial_Xpow]
  simp only [Finset.mul_sum,monomial_mul_monomial,one_mul,map_sum,eval_finsetSum,
    primitive_monomial,eval_monomial]

variable [CharZero K]

theorem clear_port {n:ℕ} (hn:0<n) (hh:n≤14) :
    ((360360/n:ℕ):K)=(360360:K)/(n:K) := by
  have hd : n∣360360 := by interval_cases n <;> decide
  apply (eq_div_iff (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))).mpr
  exact_mod_cast Nat.div_mul_cancel hd

/-- A fixed degree-four coordinate scaling avoids any need to specialize
the field coefficients of Q. -/
def scaledCoeff (Q:K[X]) (j:Fin 5) : K := Q.coeff j.val*(429:K)^(4-j.val)

theorem scaled_global_row (k:ℕ) (hk:k≤4) (Z Q:K[X]) (dz:Z.natDegree≤5) (dq:Q.natDegree≤4) :
    (∑j:Fin 5, globalEntry (Z.scaleRoots 429).coeff k j.val * scaledCoeff Q j) =
    (429:K)^(Z.natDegree+4+k+1)*(360360:K)*(primitive ((X^k*Z)*Q)).eval 1 := by
  rw [primitive_global_sum _ _ _ dz dq]
  change (∑j:Fin 5, (globalEntry (Z.scaleRoots 429).coeff k j.val *
      (Q.coeff j.val * 429^(4-j.val))))=_
  rw [Fin.sum_univ_eq_sum_range (fun j=>globalEntry (Z.scaleRoots 429).coeff k j*(Q.coeff j*429^(4-j)))]
  simp only [globalEntry,Finset.sum_mul,Finset.mul_sum,coeff_scaleRoots]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  have dj:j<5:=Finset.mem_range.mp hj
  have di:i<6:=Finset.mem_range.mp hi
  rw [clear_port (by omega : 0<k+i+j+1) (by omega)]
  by_cases h : i≤Z.natDegree
  · have exp : (429:K)^(Z.natDegree-i)*429^(k+i+j+1)*429^(4-j)=429^(Z.natDegree+4+k+1) := by
      rw [←pow_add,←pow_add]; congr 1; omega
    rw [←exp]; ring
  · rw [coeff_eq_zero_of_natDegree_lt (Nat.lt_of_not_ge h)]; ring

theorem scaled_local_row (k:ℕ) (hk:k≤2) (Q:K[X]) (dq:Q.natDegree≤4) (u:K) :
    (∑j:Fin 5, localEntry ((429:K)*u) k j.val * scaledCoeff Q j) =
    (429:K)^(4+k+1)*360360*(primitive (X^k*Q)).eval u := by
  rw [primitive_local_sum _ _ dq]
  change (∑j:Fin 5, localEntry ((429:K)*u) k j.val*(Q.coeff j.val*429^(4-j.val)))=_
  rw [Fin.sum_univ_eq_sum_range (fun j=>localEntry ((429:K)*u) k j*(Q.coeff j*429^(4-j)))]
  simp only [localEntry,mul_pow,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have dj:j<5:=Finset.mem_range.mp hj
  rw [clear_port (by omega : 0<k+j+1) (by omega)]
  have e : (429:K)^(k+j+1)*429^(4-j)=429^(4+k+1):=by rw [←pow_add]; congr 1; omega
  rw [←e]; ring

end RKCert.PortRank
