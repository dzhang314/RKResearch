module

public import RKCert.ReviewedNative.ERK8FourOffCleanShapeAlgebra
public import RKCert.ReviewedNative.ERK8PaidLobatto

@[expose] public section

/-! # Raw four-off clean head over every paid field
No division by the scale, the clean E scalar, or the quadratic leading
coefficient occurs. In particular this theorem leaves the exceptional
characteristic-eleven degeneration in scope. -/
namespace RKResearch.Certified.Graded.ERK8PaidField

open Polynomial Module RKResearch RKCert.Endpoint
open LobattoEight
open RKResearch.Certified.Graded.MultiOff.FourOff8CleanShape
open RKResearch.Certified.Graded.MultiOff.FourOff8Scalar
open scoped Matrix Classical

variable {K : Type*} [Field K] {s : ℕ}
  {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}

structure RawPaidShape (P : K[X]) (h x z theta k : K) : Prop where
  identity : P = C theta * cleanPair x z +
    C k * (C 5 * X^2 - C (4*x+3*h) * X + C (2*h*x))
  ratio : theta * cleanE h x z = k * cleanNumer h x

/-- This derivation reads the two paid clean evaluations as five
Hermite zeros, then differentiates the forced quintic factor. -/
theorem raw_shape_from_primitive (ho : HasOrder 8 A b)
    (P : K[X]) (hp : P.natDegree≤2) {h x z theta : K}
    (h0 : h≠0) (x0 : x≠0) (xh : x≠h)
    (Hh : (primitive (tapFactor h*P)).eval h = theta*(primitive (quartic h x z)).eval h)
    (Hx : (primitive (tapFactor h*P)).eval x = theta*(primitive (quartic h x z)).eval x)
    (XP : (primitive (X*P)).eval h=0) :
    ∃ k, RawPaidShape P h x z theta k := by
  let U := P - C theta * cleanPair x z
  let B := tapFactor h
  let F := primitive (B*U)
  have udeg : U.natDegree≤2 := natDegree_sub_le_of_le hp
    ((natDegree_C_mul_le theta _).trans (cleanPair_degree_le x z))
  have dBU : (B*U).natDegree≤4 := natDegree_mul_le_of_le (tapFactor_degree_le h) udeg
  have dF : F.natDegree≤5 := primitive_natDegree_le dBU
  have der : F.derivative=B*U :=
    primitive_derivative_paid (fun n hn hp => (ho.natCast_isUnit hn (by omega)).ne_zero)
  have fe (r : K) : F.eval r =
      (primitive (tapFactor h*P)).eval r-theta*(primitive (quartic h x z)).eval r := by
    have eq : B*U=tapFactor h*P-C theta*quartic h x z := by
      dsimp only [B,U,quartic]
      ring
    dsimp only [F]
    rw [eq,map_sub,eval_sub,←smul_eq_C_mul,map_smul,eval_smul,smul_eq_mul]
  have at0 : F.IsRoot 0 := by
    rw [IsRoot,←coeff_zero_eq_eval_zero,show F=primitive (B*U) from rfl,primitive_coeff_zero]
  have ath : F.IsRoot h := by rw [IsRoot,fe,Hh,sub_self]
  have atx : F.IsRoot x := by rw [IsRoot,fe,Hx,sub_self]
  let T : Finset K := {0,h}
  have xt : x∉T := by simp [T,x0,xh]
  have he : nodalHull T = B := by
    have hn : (0:K)∉({h}:Finset K) := by simp [Ne.symm h0]
    simp [T,nodalHull,Finset.prod_insert hn,B,tapFactor]
  have D : B^2*(X-C x) ∣ F := by
    rw [←he]
    apply nodalHull_sq_extra_dvd T xt _ _ atx
    · intro a ha
      simp only [T,Finset.mem_insert,Finset.mem_singleton] at ha
      rcases ha with rfl|rfl
      · exact at0
      · exact ath
    · intro a ha
      rw [der,IsRoot,eval_mul,←he,nodalHull_eval_of_mem ha,zero_mul]
  have Bnz : B≠0 := by
    rw [←he]
    exact (monic_nodalHull T).ne_zero
  have dB : B.natDegree=2 := by rw [←he,natDegree_nodalHull]; simp [T,Ne.symm h0]
  let D0 := B^2*(X-C x)
  have nd0 : D0≠0 := mul_ne_zero (pow_ne_zero _ Bnz) (X_sub_C_ne_zero _)
  have d0 : D0.natDegree=5 := by
    rw [show D0=B^2*(X-C x) from rfl,natDegree_mul (pow_ne_zero _ Bnz) (X_sub_C_ne_zero _),
      natDegree_pow,dB,natDegree_X_sub_C]
  obtain ⟨W,hW⟩ := D
  have W0 : W.natDegree=0 := by
    by_cases hW0 : W=0
    · simp [hW0]
    have nd := natDegree_mul (p:=D0) (q:=W) nd0 hW0
    have f : F=D0*W := hW
    rw [←f,d0] at nd
    omega
  let κ := W.coeff 0
  have convW : W=C κ := eq_C_of_natDegree_eq_zero W0
  have dFshape : F= C κ * (B^2*(X-C x)) := by rw [hW,convW]; ring
  have dy : B*U = B*(C κ*(C 5*X^2-C (4*x+3*h)*X+C (2*h*x))) := by
    rw [←der,dFshape]
    simp only [Polynomial.derivative_mul,Polynomial.derivative_C,Polynomial.derivative_X,
      Polynomial.derivative_sub,Polynomial.derivative_pow,B,tapFactor,zero_mul,zero_add,
      sub_zero,map_add,map_mul,Polynomial.C_ofNat,map_natCast,Nat.cast_ofNat]
    ring
  have eqU := mul_left_cancel₀ Bnz dy
  have pd : P = C theta*cleanPair x z+C κ*(C 5*X^2-C (4*x+3*h)*X+C (2*h*x)) := by
    dsimp only [U] at eqU
    linear_combination eqU
  have c0 : P.coeff 0=theta*(x*z)+κ*(2*h*x) := by
    rw [pd]
    simp [cleanPair, coeff_X, coeff_mul, Finset.Nat.antidiagonal_succ] <;> ring
  have c1 : P.coeff 1= -theta*(x+z)-κ*(4*x+3*h) := by
    rw [pd]
    simp [cleanPair, coeff_X, coeff_mul, Finset.Nat.antidiagonal_succ] <;> ring
  have c2 : P.coeff 2=theta+5*κ := by
    rw [pd]
    simp [cleanPair, coeff_X, coeff_mul, Finset.Nat.antidiagonal_succ] <;> ring
  rw [primitive_eval_X_quadratic P hp] at XP
  have n3 : (3:K)≠0 := (ho.natCast_isUnit (n:=3) (by decide) (by decide)).ne_zero
  have n4 : (4:K)≠0 := (ho.natCast_isUnit (n:=4) (by decide) (by decide)).ne_zero
  have e0 : (P.coeff 0*h^2/2)*2=P.coeff 0*h^2 := div_mul_cancel₀ _ (two_ne ho)
  have e1 : (P.coeff 1*h^3/3)*3=P.coeff 1*h^3 := div_mul_cancel₀ _ n3
  have e2 : (P.coeff 2*h^4/4)*4=P.coeff 2*h^4 := div_mul_cancel₀ _ n4
  have rat : h^2*(theta*cleanE h x z-κ*cleanNumer h x)=0 := by
    unfold cleanE cleanNumer
    linear_combination 12*XP-6*e0-4*e1-3*e2-6*h^2*c0-4*h^3*c1-3*h^4*c2
  exact ⟨κ,pd,sub_eq_zero.mp ((mul_eq_zero.mp rat).resolve_left (pow_ne_zero _ h0))⟩

end RKResearch.Certified.Graded.ERK8PaidField
