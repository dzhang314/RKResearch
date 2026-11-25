module

public import RKCert.ReviewedNative.NativePencilCubicUniform
public import RKCert.ReviewedNative.NativePencilQuarticUniform
public import RKCert.ReviewedNative.NativeLobatto43
public import RKCert.ReviewedNative.GradedPrimitives
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Literal physical polynomial endpoints for the early marked degree-seven pencil

Only the genuinely paid row/primitive conditions are needed. This scalar
leaf is not itself a tableau theorem. `lobattoValue`, `radauQuotient`,
`cubicD`, `cubicN`, and `primitive` are the original reviewed functions. -/
namespace RKResearch.Certified.Graded.NativePencilPorts
open Polynomial NativePencilProjection NativeLobatto NativeHornerWitness
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

/-- H(X) = F(t) j(tX) − j(t) F(tX). -/
def pencilContrast (t : K) : K[X] :=
  lobattoValue (C t) * radauQuotient (C t * X) - radauQuotient (C t) * lobattoValue (C t * X)

/-- The normalized nonzero candidate left by the two lower moments. -/
def cubicMask (z : K) : K[X] :=
  let Z := C z
  (12*Z-15*Z^2) + (60*Z^2-24*Z-18)*X - 10*(5*Z^2+4*Z-6)*X^2 + 15*(4*Z-3)*X^3

private theorem contrast_eval (t x : K) :
    (pencilContrast t).eval x =
      lobattoValue t * radauQuotient (t*x) - radauQuotient t * lobattoValue (t*x) := by
  simp only [pencilContrast,lobattoValue,radauQuotient,eval_mul,eval_add,eval_sub,
    eval_pow,eval_C,eval_X,eval_ofNat,eval_one]

private theorem apply_literal_model (l : List (List (List ℤ))) (z t : K)
    (P : K[X]) (h : ∀ x : K, foldX z t x l = P.eval x) :
    (packX l).map (tEval z t) = P := by
  letI : Infinite K := Infinite.of_injective (fun n : ℕ => (n : K)) Nat.cast_injective
  apply Polynomial.funext
  intro x
  rw [Polynomial.eval_map,eval_packX]
  exact h x

set_option maxHeartbeats 3000000 in
private theorem contrast_model (z t : K) :
    (packX NativePencilCubicInteger.obstructionCode).map (tEval z t) = pencilContrast t := by
  apply apply_literal_model
  intro x
  rw [contrast_eval]
  simp only [NativePencilCubicInteger.obstructionCode,foldX,foldT,foldZ,horner,
    lobattoValue,radauQuotient,Int.cast_zero,mul_zero,zero_mul,add_zero,zero_add]
  ring

private theorem profile_model (z t : K) :
    (packX NativePencilCubicInteger.profileCode).map (tEval z t) = cubicMask z := by
  apply apply_literal_model
  intro x
  simp only [NativePencilCubicInteger.profileCode,foldX,foldT,foldZ,horner,cubicMask,
    eval_C,eval_X,eval_sub,eval_mul,eval_add,eval_pow,eval_ofNat,
    Int.cast_zero,mul_zero,zero_mul,add_zero,zero_add]
  ring

set_option maxHeartbeats 3000000 in
private theorem cubic_first_model (z t : K) :
    (z-1)*NativePencilCubicInteger.firstPort z t =
      cubicD z*lobattoValue (t*z)+z^3*cubicN z*lobattoValue t := by
  change (z-1)*foldT z t NativePencilCubicInteger.firstCode = _
  simp [NativePencilCubicInteger.firstCode,foldT,foldZ,horner,cubicD,cubicN,lobattoValue] <;> ring

set_option maxHeartbeats 3000000 in
private theorem cubic_second_model (z t : K) :
    ((z-1)*t)*NativePencilCubicInteger.secondPort z t =
      (cubicD z*radauQuotient (t*z)+z^3*cubicN z*radauQuotient t) +
      7*(cubicD z*lobattoValue (t*z)+z^3*cubicN z*lobattoValue t) := by
  change ((z-1)*t)*foldT z t NativePencilCubicInteger.secondCode = _
  simp [NativePencilCubicInteger.secondCode,foldT,foldZ,horner,cubicD,cubicN,lobattoValue,
    radauQuotient] <;> ring

/-- The actual pair of common-leakage equations excludes any polynomial
factor shared by H and the normalized cubic over any characteristic-zero field. -/
theorem cubic_pencil_ports_coprime (z t : K) (zn : z ≠ 0) (z1 : z ≠ 1) (tn : t ≠ 0)
    (fport : cubicD z * lobattoValue (t*z) + z^3*cubicN z*lobattoValue t=0)
    (jport : cubicD z * radauQuotient (t*z) + z^3*cubicN z*radauQuotient t=0) :
    IsCoprime (pencilContrast t) (cubicMask z) := by
  have az : NativePencilCubicInteger.firstPort z t = 0 :=
    (mul_eq_zero.mp ((cubic_first_model z t).trans fport)).resolve_left (sub_ne_zero.mpr z1)
  have c0 : ((z-1)*t)*NativePencilCubicInteger.secondPort z t=0 := by
    rw [cubic_second_model,jport,fport,mul_zero,add_zero]
  have cz : NativePencilCubicInteger.secondPort z t = 0 :=
    (mul_eq_zero.mp c0).resolve_left (mul_ne_zero (sub_ne_zero.mpr z1) tn)
  have cop := NativePencilCubicUniform.scalar_coprime z t zn az cz
  rwa [contrast_model z t,profile_model z t] at cop

/-! Literal monic-division recurrence for the quartic complementary factor.
The exact remainder identity below holds even before one imposes H(z)=0. -/
def w4 (t : K) : K := t^4*(1716*lobattoValue t)
def w3 (z t : K) : K := t^3*((-5544)*lobattoValue t-132*radauQuotient t)+(1+z)*w4 t
def w2 (z t : K) : K := t^2*(6930*lobattoValue t+330*radauQuotient t)+(1+z)*w3 z t-z*w4 t
def w1 (z t : K) : K := t*((-4200)*lobattoValue t-300*radauQuotient t)+(1+z)*w2 z t-z*w3 z t
def w0 (z t : K) : K := 1260*lobattoValue t+120*radauQuotient t+(1+z)*w1 z t-z*w2 z t

def quartic (a b c d e : K) : K[X] :=
  monomial 0 a + monomial 1 b + monomial 2 c + monomial 3 d + monomial 4 e

def quarticMask (z t : K) : K[X] := quartic (w0 z t) (w1 z t) (w2 z t) (w3 z t) (w4 t)

private def m1 (a b c d e y : K) : K :=
  210*a*y^2+140*b*y^3+105*c*y^4+84*d*y^5+70*e*y^6
private def m2 (a b c d e y : K) : K :=
  140*a*y^3+105*b*y^4+84*c*y^5+70*d*y^6+60*e*y^7

private theorem first_moment (a b c d e y : K) :
    420*(primitive (X*quartic a b c d e)).eval y=m1 a b c d e y := by
  have h : 420*(primitive ((X:K[X])^1*quartic a b c d e)).eval y=m1 a b c d e y := by
    simp only [quartic,mul_add,X_pow_mul_monomial,map_add,primitive_monomial,eval_add,eval_monomial,m1]
    norm_num <;> ring
  simpa only [pow_one] using h

private theorem second_moment (a b c d e y : K) :
    420*(primitive (X^2*quartic a b c d e)).eval y=m2 a b c d e y := by
  simp only [quartic,mul_add,X_pow_mul_monomial,map_add,primitive_monomial,eval_add,eval_monomial,m2]
  norm_num <;> ring

/-- Keep the two low terms separate during scalar division. In particular the
executable coefficient comparison below has only variables z,t, not z,t,x. -/
private def remainderLin (z t : K) : K :=
  -168*lobattoValue t-20*radauQuotient t+t*((1+z)*w0 z t-z*w1 z t)

private def remainderConst (z t : K) : K :=
  7*lobattoValue t+radauQuotient t-z*t^2*w0 z t

private theorem contrast_expansion (f j t x : K) :
    f*radauQuotient (t*x)-j*lobattoValue (t*x) =
      (t^6*(1716*f))*x^6 +(t^5*((-5544)*f-132*j))*x^5 +
      (t^4*(6930*f+330*j))*x^4 +(t^3*((-4200)*f-300*j))*x^3 +
      (t^2*(1260*f+120*j))*x^2 + (t*((-168)*f-20*j))*x + (7*f+j) := by
  unfold radauQuotient lobattoValue
  ring

set_option maxHeartbeats 1500000 in
private theorem affine_remainder (z t x : K) :
    (pencilContrast t).eval x =
      (x-1)*(x-z)*t^2*(quarticMask z t).eval x + (t*remainderLin z t)*x +
        remainderConst z t := by
  rw [contrast_eval,contrast_expansion]
  have e4 : t^6*(1716*lobattoValue t)=t^2*w4 t := by unfold w4; ring
  have e3 : t^5*((-5544)*lobattoValue t-132*radauQuotient t) =
      t^2*(w3 z t-(1+z)*w4 t) := by unfold w3; ring
  have e2 : t^4*(6930*lobattoValue t+330*radauQuotient t) =
      t^2*(w2 z t-(1+z)*w3 z t+z*w4 t) := by unfold w2; ring
  have e1 : t^3*((-4200)*lobattoValue t-300*radauQuotient t) =
      t^2*(w1 z t-(1+z)*w2 z t+z*w3 z t) := by unfold w1; ring
  have e0 : t^2*(1260*lobattoValue t+120*radauQuotient t) =
      t^2*(w0 z t-(1+z)*w1 z t+z*w2 z t) := by unfold w0; ring
  rw [e4,e3,e2,e1,e0]
  simp only [quarticMask,quartic,remainderLin,remainderConst,eval_add,eval_monomial,
    pow_zero,pow_one,mul_one]
  ring

set_option maxHeartbeats 3000000 in
private theorem remainderLin_eq_secondPort (z t : K) :
    remainderLin z t = NativePencilQuarticInteger.secondPort z t := by
  change remainderLin z t = foldT z t NativePencilQuarticInteger.secondCode
  simp [remainderLin,NativePencilQuarticInteger.secondCode,foldT,foldZ,horner,
    w0,w1,w2,w3,w4,lobattoValue,radauQuotient] <;> ring

/-- The quotient recurrence pays exactly the alleged complementary quartic, with its
potential linear remainder displayed. It does not assume the t,z ports. -/
theorem quartic_division_identity (z t : K) :
    pencilContrast t = (X-1)*(X-C z)*(C t)^2*quarticMask z t +
      (X-1)*C (t * NativePencilQuarticInteger.secondPort z t) := by
  have h := affine_remainder z t 1
  rw [contrast_eval] at h
  simp only [mul_one,mul_comm (lobattoValue t) (radauQuotient t),sub_self,zero_mul,zero_add] at h
  have constant : remainderConst z t = -(t*remainderLin z t) :=
    eq_neg_of_add_eq_zero_right h.symm
  letI : Infinite K := Infinite.of_injective (fun n : ℕ => (n : K)) Nat.cast_injective
  apply Polynomial.funext
  intro x
  rw [affine_remainder,constant,← remainderLin_eq_secondPort z t]
  simp only [eval_add,eval_mul,eval_sub,eval_pow,eval_X,eval_C,eval_one]
  ring

set_option maxHeartbeats 3000000 in
private theorem quartic_first_model (z t : K) :
    NativePencilQuarticInteger.firstPort z t =
      420*(primitive (X*quarticMask z t)).eval 1 := by
  change foldT z t NativePencilQuarticInteger.firstCode = _
  rw [quarticMask,first_moment]
  simp [NativePencilQuarticInteger.firstCode,foldT,foldZ,horner,m1,w0,w1,w2,w3,w4,
    lobattoValue,radauQuotient] <;> ring

private theorem quartic_second_model (z t : K) :
    ((z-1)*t)*NativePencilQuarticInteger.secondPort z t =
      lobattoValue t*radauQuotient (t*z)-radauQuotient t*lobattoValue (t*z) := by
  have h := congrArg (fun P : K[X] => P.eval z) (quartic_division_identity z t)
  simp only [contrast_eval,eval_add,eval_mul,eval_sub,eval_X,eval_C,eval_one,
    sub_self,mul_zero,zero_mul,zero_add] at h
  simpa only [mul_assoc] using h.symm

set_option maxHeartbeats 8000000 in
private theorem quartic_obstruction_literal (z t : K) :
    z*foldT z t (NativePencilQuarticInteger.obstructionCode.getD 0 []) =
      z*lobattoValue (t*z)*m2 (w0 z t) (w1 z t) (w2 z t) (w3 z t) (w4 t) 1 -
        lobattoValue t*(m2 (w0 z t) (w1 z t) (w2 z t) (w3 z t) (w4 t) z -
          m1 (w0 z t) (w1 z t) (w2 z t) (w3 z t) (w4 t) z) := by
  simp [NativePencilQuarticInteger.obstructionCode,foldT,foldZ,horner,m1,m2,
    w0,w1,w2,w3,w4,lobattoValue,radauQuotient] <;> ring

private theorem quartic_obstruction_model (z t : K) :
    z*foldT z t (NativePencilQuarticInteger.obstructionCode.getD 0 []) =
      420*(z*lobattoValue (t*z)*(primitive (X^2*quarticMask z t)).eval 1 -
        lobattoValue t*((primitive (X^2*quarticMask z t)).eval z -
          (primitive (X*quarticMask z t)).eval z)) := by
  rw [quartic_obstruction_literal,quarticMask]
  have s1 := (first_moment (w0 z t) (w1 z t) (w2 z t) (w3 z t) (w4 t) z).symm
  have s2 := (second_moment (w0 z t) (w1 z t) (w2 z t) (w3 z t) (w4 t) z).symm
  have s3 := (second_moment (w0 z t) (w1 z t) (w2 z t) (w3 z t) (w4 t) 1).symm
  rw [s1,s2,s3]
  ring

/-- At a genuine common nonzero pair of pencil knots, the first weighted primitive
and the shared second leakage test cannot both vanish for this complementary
quartic. Cross multiplication leaves no variable in a denominator. -/
theorem quartic_pencil_ports_incompatible (z t : K) (z1 : z≠1) (zn : z≠0) (tn : t≠0)
    (pair : lobattoValue t*radauQuotient (t*z)-radauQuotient t*lobattoValue (t*z)=0)
    (first : (primitive (X*quarticMask z t)).eval 1=0) :
    z*lobattoValue (t*z)*(primitive (X^2*quarticMask z t)).eval 1 -
      lobattoValue t*((primitive (X^2*quarticMask z t)).eval z-
        (primitive (X*quarticMask z t)).eval z) ≠ 0 := by
  have az : NativePencilQuarticInteger.firstPort z t = 0 := by
    rw [quartic_first_model,first,mul_zero]
  have mz : NativePencilQuarticInteger.secondPort z t = 0 :=
    (mul_eq_zero.mp ((quartic_second_model z t).trans pair)).resolve_left
      (mul_ne_zero (sub_ne_zero.mpr z1) tn)
  have bn := NativePencilQuarticUniform.scalar_ne_zero z t az mz
  intro zero
  have vanish : z*foldT z t (NativePencilQuarticInteger.obstructionCode.getD 0 [])=0 := by
    rw [quartic_obstruction_model,zero,mul_zero]
  exact (mul_ne_zero zn bn) vanish

end
end RKResearch.Certified.Graded.NativePencilPorts
