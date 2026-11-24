module
public import RKCert.DirkLobattoQuadrature

@[expose] public section
namespace RKCert.Paired.Terminal
open RKCert.Endpoint Polynomial
variable {K : Type*} [Field K] [CharZero K]
noncomputable section

/-- The ordinary scalar moment used in a paid tail. -/
def tailMoment (n : ℕ) (H : K[X]) : K := integral (X^n*H)

omit [CharZero K] in
/-- Testing a polynomial multiplier is coefficientwise convolution of moments. -/
theorem tailMoment_mul (k : ℕ) (Q H : K[X]) :
    tailMoment k (Q*H) = ∑ i ∈ Finset.range (Q.natDegree+1), Q.coeff i * tailMoment (k+i) H := by
  let L : K[X] →ₗ[K] K := integral.comp (LinearMap.mulLeft K (X^k*H))
  change integral (X^k*(Q*H))=_
  rw [show X^k*(Q*H)=(X^k*H)*Q by ring]
  change L Q=_
  conv_lhs => rw [Q.as_sum_range]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [show monomial i (Q.coeff i)=Q.coeff i • (X^i:K[X]) by
    rw [smul_eq_C_mul,C_mul_X_pow_eq_monomial],map_smul,smul_eq_mul]
  congr 1
  change integral ((X^k*H)*X^i)=integral (X^(k+i)*H)
  rw [pow_add]; ring_nf

/-- With both endpoints zero, degree m needs only m−1 low moments. Apply
ordinary nondegenerate moment detection to the derivative after integration
by parts; nothing about an order on the scalar field is required. -/
theorem two_endpoint_moment_detect {m : ℕ} (H : K[X]) (dH : H.natDegree≤m)
    (h0 : H.eval 0=0) (h1 : H.eval 1=0)
    (pay : ∀ j : ℕ, j+2≤m → tailMoment j H=0) : H=0 := by
  have hcoeff : H.coeff 0=0 := by simpa only [coeff_zero_eq_eval_zero] using h0
  have derivative_test (r : ℕ) (hr : r≤m-1) : tailMoment r H.derivative=0 := by
    cases r with
    | zero =>
      simpa only [tailMoment,pow_zero,one_mul,integral_eq,primitive_derivative H hcoeff] using h1
    | succ j =>
      let T : K[X] := X^(j+1)*H
      have t0 : T.coeff 0=0 := by simp [T,coeff_zero_eq_eval_zero,h0]
      have t1 : T.eval 1=0 := by simp [T,h1]
      have dt : integral T.derivative=0 := by rw [integral_eq,primitive_derivative _ t0,t1]
      have de : T.derivative=((j+1:ℕ):K) • (X^j*H) + X^(j+1)*H.derivative := by
        simp [T,derivative_mul,derivative_X_pow_succ,smul_eq_C_mul,mul_assoc]
      rw [de,map_add,map_smul,smul_eq_mul,show integral (X^j*H)=0 from pay j (by omega),mul_zero,zero_add] at dt
      exact dt
  have dh : H.derivative=0 := primitive_shift_detect H.derivative (k:=0)
    ((natDegree_derivative_le H).trans (Nat.sub_le_sub_right dH 1)) 1 one_ne_zero (fun r => by
      have e:=derivative_test r.val (by have:=r.isLt; omega)
      simpa only [tailMoment,integral_eq,formalPrimitive_eq_treePrimitive,zero_add] using e)
  rw [←primitive_derivative H hcoeff,dh,map_zero]

end
end RKCert.Paired.Terminal
