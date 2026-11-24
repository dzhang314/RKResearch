module

public import RKCert.ReviewedNative.JacobiMomentPorts
import RKCert.EndpointJacobiTwo

@[expose] public section

/-! # Signed Jacobi endpoint masses without a coefficient table

The weight is algebraic formal integration. One Legendre symmetry and
the shared orthogonality theorem give the two exact endpoint values
for every positive degree, independently of any tableau. -/
namespace RKCert.ReviewedNative.JacobiMoments

open Polynomial RKCert.Endpoint RKCert.Paired
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

theorem x_signedSlope_degree (m : ℕ) (hm : 0<m) :
    (X*signedSlope K m).natDegree=m := by
  have sign : (-1:K)^m≠0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  have der : (mappedLegendre K m).derivative≠0 :=
    derivative_ne_zero.mpr (by rw [mappedLegendre_degree];omega)
  have e : signedSlope K m = C ((-1:K)^m)*(mappedLegendre K m).derivative := by
    rw [signedSlope,mappedLegendre,Polynomial.derivative_map]
  rw [e,natDegree_X_mul (mul_ne_zero (C_ne_zero.mpr sign) der),natDegree_C_mul sign,
    natDegree_derivative,mappedLegendre_degree]
  omega

omit [CharZero K] in
private theorem mapped_reflection (m : ℕ) :
    C ((-1:K)^m)*(mappedLegendre K m).comp (1-X)=mappedLegendre K m := by
  have h := congrArg (Polynomial.map (Int.castRingHom K))
    (neg_one_pow_mul_shiftedLegendre_comp_one_sub_X_eq m)
  simp only [Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_neg,Polynomial.map_one,
    Polynomial.map_sub,Polynomial.map_X,Polynomial.map_comp] at h
  have ss : (C ((-1:K)^m) : K[X])=(-1:K[X])^m := by simp
  rw [ss]
  exact h

omit [CharZero K] in
private theorem mapped_origin (m : ℕ) : (mappedLegendre K m).eval 0=1 := by
  rw [←coeff_zero_eq_eval_zero,mappedLegendre,coeff_map,coeff_shiftedLegendre]
  simp

private theorem mapped_derivative_origin (m : ℕ) :
    (mappedLegendre K m).derivative.eval 0=-((m:K)*((m:K)+1)) := by
  rw [←coeff_zero_eq_eval_zero,coeff_derivative,mappedLegendre,coeff_map,coeff_shiftedLegendre]
  simp [Nat.choose_one_right,Nat.choose_succ_self_right]

/-- The signed slope has the universal derivative value m(m+1) at one. -/
theorem signedSlope_at_one (m : ℕ) :
    (signedSlope K m).eval 1=(m:K)*((m:K)+1) := by
  have h := congrArg Polynomial.derivative (mapped_reflection (K:=K) m)
  rw [derivative_C_mul,derivative_comp_one_sub_X] at h
  have v := congrArg (Polynomial.eval (0:K)) h
  simp only [eval_mul,eval_C,eval_neg,eval_comp,eval_sub,eval_one,eval_X,sub_zero,
    mapped_derivative_origin] at v
  unfold signedSlope
  rw [eval_mul,eval_C,←derivative_map]
  change _*(mappedLegendre K m).derivative.eval 1=_
  linear_combination -v

/-- The normalized primitive of X times the signed slope is one at one. -/
theorem formalPrimitive_x_signedSlope_at_one (m : ℕ) (hm : 0<m) :
    (formalPrimitive (X*signedSlope K m)).eval 1=1 := by
  let J := mappedLegendre K m
  let t := (-1:K)^m
  have heval := congrArg (Polynomial.eval (0:K)) (mapped_reflection (K:=K) m)
  simp only [eval_mul,eval_C,eval_comp,eval_sub,eval_one,eval_X,sub_zero,mapped_origin] at heval
  have p := unitIntegral_derivative (X*J)
  have orth : unitIntegral J=0 := by
    have e := mappedLegendre_orthogonal (K:=K) m 1 (by simpa using hm)
    simpa only [one_mul] using e
  rw [derivative_mul,derivative_X,one_mul,map_add,orth,zero_add,eval_mul,eval_mul,eval_X,
    eval_X,zero_mul,sub_zero,one_mul] at p
  have slope : signedSlope K m=C t*J.derivative := by
    dsimp only [t,J]
    rw [signedSlope,mappedLegendre,Polynomial.derivative_map]
  rw [←unitIntegral_apply,slope,show X*(C t*J.derivative)=t • (X*J.derivative) by
    rw [smul_eq_C_mul];ring,map_smul,smul_eq_mul,p]
  exact heval

end
end RKCert.ReviewedNative.JacobiMoments
