module

public import RKCert.DirkTrace

@[expose] public section

/-! # One endpoint and shifted Hilbert tests

Use the known zero sum of the coefficients to eliminate the constant
Cauchy column. The shifted Hilbert kernel certifies the rest, including
both one- and two-endpoint-weighted tests, over any char-zero field.
-/
namespace RKCert.Paired
open RKCert.Endpoint Polynomial
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

set_option maxHeartbeats 560000 in
theorem endpoint_one_primitive_shift_detect (T : K[X]) {d k : ℕ}
    (hT : T.natDegree≤d+1) (h₁ : T.eval 1=0)
    (he : ∀ i : Fin (d+1), (formalPrimitive (X^(k+i.val)*T)).eval 1=0) : T=0 := by
  let v : Fin (d+2)→K := fun j => T.coeff j.val
  have total : ∑ j,v j=0 := by
    have h := T.eval_eq_sum_range' (x:=1) (by omega : T.natDegree<d+2)
    rw [Finset.sum_range,h₁] at h
    simpa only [v,one_pow,mul_one] using h.symm
  let u : Fin (d+1)→K := fun j => ((j.val+1:ℕ):K)*v j.succ
  have eqn (i : Fin (d+1)) :
      (∑ j : Fin (d+2),v j/((k+i.val+j.val+1:ℕ):K))=0 := by
    have h := he i
    rw [primitive_eval_power_mul _ _ _ hT] at h
    simpa only [v,one_pow,mul_one] using h
  have reduced (i : Fin (d+1)) :
      (∑ j : Fin (d+1),u j/((i.val+j.val+(k+2):ℕ):K))=0 := by
    have h := congrArg (fun a : K => ((k+i.val+1:ℕ):K)*a) (eqn i)
    rw [mul_zero,Finset.mul_sum] at h
    have term (j : Fin (d+2)) :
        ((k+i.val+1:ℕ):K)*(v j/((k+i.val+j.val+1:ℕ):K)) =
          v j-((j.val:K)*v j)/((k+i.val+j.val+1:ℕ):K) := by
      have nz : ((k+i.val+j.val+1:ℕ):K)≠0 := Nat.cast_ne_zero.mpr (by omega)
      field_simp [nz]
      push_cast
      ring
    rw [Finset.sum_congr rfl (fun j _ => term j),Finset.sum_sub_distrib,total,zero_sub,
      neg_eq_zero,Fin.sum_univ_succ] at h
    have htail : (∑ j : Fin (d+1), (j.succ.val:K)*v j.succ/((k+i.val+j.succ.val+1:ℕ):K))=0 := by
      simpa only [Fin.val_zero,Nat.cast_zero,zero_mul,zero_div,zero_add] using h
    rw [←htail]
    apply Finset.sum_congr rfl
    intro j _
    change ((j.val+1:ℕ):K)*v j.succ/((i.val+j.val+(k+2):ℕ):K)=_
    rw [show i.val+j.val+(k+2)=k+i.val+j.succ.val+1 by simp only [Fin.val_succ]; omega]
    rfl
  have uz := shifted_hilbert_kernel (k+2) (by omega) u reduced
  have tail (j : Fin (d+1)) : v j.succ=0 := by
    have e := congrFun uz j
    change ((j.val+1:ℕ):K)*v j.succ=0 at e
    exact (mul_eq_zero.mp e).resolve_left (Nat.cast_ne_zero.mpr (by omega))
  have first : v 0=0 := by
    rw [Fin.sum_univ_succ] at total
    simpa only [tail,Finset.sum_const_zero,add_zero] using total
  ext n
  by_cases h : n<d+2
  · let j : Fin (d+2) := ⟨n,h⟩
    have val : v j=0 := Fin.cases first tail j
    simpa only [coeff_zero,v,j] using val
  · rw [coeff_zero,coeff_eq_zero_of_natDegree_lt (by omega)]

/-- No nonzero scalar polynomial of paid degree at most d can be invisible
to the indicated unit moments with weight x^k(1-x). -/
theorem two_end_weight_primitive_detect (P : K[X]) {d k : ℕ} (hP : P.natDegree≤d)
    (he : ∀ i : Fin (d+1),(formalPrimitive (X^(k+i.val)*((1-X)*P))).eval 1=0) : P=0 := by
  have h : (1-X)*P=0 := endpoint_one_primitive_shift_detect _ (k:=k)
    (natDegree_mul_le.trans (by
      have h : (1-X:K[X]).natDegree≤1 := (natDegree_sub_le _ _).trans (by simp)
      omega)) (by simp) he
  exact (mul_eq_zero.mp h).resolve_left (by
    intro e
    have hd := congrArg (fun Q : K[X] => Q.coeff 1) e
    norm_num [coeff_sub,coeff_one,coeff_X] at hd)

end
end RKCert.Paired
