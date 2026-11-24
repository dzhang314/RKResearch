module
public import RKCert.RadauGridLift
public import RKCert.Dirk15SignatureAlgebra
@[expose] public section
namespace RKCert.Paired.EarlyFifteen
open Polynomial RKCert.Endpoint RKCert.Paired.Signature
open RKCert.FixedPolynomial.Radau77569

private noncomputable def ratioExpr : MvPolynomial (Option (Fin 2)) ℤ :=
  15 * (MvPolynomial.X (some 1))^2 - 24 * MvPolynomial.X (some 1) * MvPolynomial.X (some 0)
  + 10 * (MvPolynomial.X (some 0))^2

private theorem ratioExpr_eval {R:Type*} [CommRing R] (a:Option (Fin 2)→R) :
    ratioExpr.eval₂ (Int.castRingHom R) a=15*(a (some 1))^2-24*a (some 1)*a (some 0)+10*(a (some 0))^2:=by
  change MvPolynomial.eval₂Hom (Int.castRingHom R) a ratioExpr=_
  simp [ratioExpr]

set_option maxRecDepth 10000 in
private theorem mod_ratio (i j:Fin 7) :
    15*(scaledRoot j.succ)^2-24*scaledRoot j.succ*scaledRoot i.succ+10*(scaledRoot i.succ)^2≠0:=by
  fin_cases i <;> fin_cases j <;> decide

variable {K:Type*} [Field K] [CharZero K]

/-- The exceptional quadratic from the degree-four 3+2 primitive gate
cannot occur at two nonzero clocks on the fixed order-15 forward grid.
Only integral fixed numerical roots, not tableau coefficients, specialize. -/
theorem fixed_ratio_ne {u v:K} (un:u≠0) (vn:v≠0)
    (ur:(radauLeft7:K[X]).eval u=0) (vr:(radauLeft7:K[X]).eval v=0) :
    15*v^2-24*v*u+10*u^2≠0:=by
  intro eq
  let a:Fin 2→K:=![u,v]
  obtain ⟨L⟩:=exists_grid_lift a (by intro i;fin_cases i <;> exact Or.inr (by first | exact ur | exact vr))
  have eqin:ratioExpr.eval₂ (Int.castRingHom K) (scaledInput a)=0:=by
    rw [ratioExpr_eval]
    change 15*(((-51480:ℤ):K)*v)^2-24*(((-51480:ℤ):K)*v)*(((-51480:ℤ):K)*u)
      +10*(((-51480:ℤ):K)*u)^2=0
    linear_combination (((-51480:ℤ):K)^2)*eq
  have z:=L.specialization.preserves ratioExpr eqin
  rw [ratioExpr_eval,L.decoded 0,L.decoded 1] at z
  obtain ⟨i,ei⟩:=Fin.eq_succ_of_ne_zero (L.nonorigin 0 un)
  obtain ⟨j,ej⟩:=Fin.eq_succ_of_ne_zero (L.nonorigin 1 vn)
  rw [ei,ej] at z
  have hz:L.specialization.embed (15*(scaledRoot j.succ)^2-24*scaledRoot j.succ*scaledRoot i.succ+
      10*(scaledRoot i.succ)^2)=0:=by simpa only [map_add,map_sub,map_mul,map_pow,map_ofNat] using z
  exact mod_ratio i j (L.specialization.embed.injective (by rwa [map_zero]))

private theorem paid_affine (P:K[X]) (u v:K) (k:ℕ) :
    paidMoment ((X-C u)*P) v k=paidMoment P v (k+1)-u*paidMoment P v k:=by
  unfold paidMoment
  have h:X^k*((X-C u)*P)=X^(k+1)*P-u • (X^k*P):=by
    rw [pow_succ,smul_eq_C_mul];ring
  change (formalPrimitiveLinear _).eval v=_
  rw [h,map_sub,map_smul,smul_eq_C_mul,eval_sub,eval_mul,eval_C]
  rfl

set_option maxHeartbeats 1000000 in
/-- Degree-four 3+2 moment detection at two nonzero distinct fixed-grid
clocks. Over a general characteristic-zero field, the finite ratio
certificate is essential; we do not use a sign argument over that field. -/
theorem quartic_three_two_impossible (P:K[X]) (pn:P≠0) (dp:P.natDegree≤4)
    {u v:K} (un:u≠0) (vn:v≠0) (vu:v≠u)
    (ur:(radauLeft7:K[X]).eval u=0) (vr:(radauLeft7:K[X]).eval v=0)
    (f₁:paidMoment P u 1=0) (f₂:paidMoment P u 2=0) (f₃:paidMoment P u 3=0)
    (g₁:paidMoment ((X-C u)*P) v 1=0)
    (g₂:paidMoment ((X-C u)*P) v 2=0):False:=by
  let a (j:Fin 5):K:=P.coeff j.val*u^j.val
  have expand (t:K) (k:ℕ) :
      paidMoment P (u*t) k=(u*t)^(k+1)*∑ j:Fin 5,a j*t^j.val/((k+j.val+1:ℕ):K):=by
    rw [paidMoment,primitive_eval_power_mul _ _ _ dp,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [show k+j.val+1=k+1+j.val by omega,pow_add,mul_pow]
    unfold a
    rw [div_eq_mul_inv,div_eq_mul_inv]
    ring
  have rows (k:ℕ) (z:paidMoment P u k=0) : (∑j:Fin 5,a j/((k+j.val+1:ℕ):K))=0:=by
    have h:=expand 1 k
    simp only [mul_one,one_pow] at h
    rw [z] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero _ un)
  have f1:=rows 1 f₁
  have f2:=rows 2 f₂
  have f3:=rows 3 f₃
  norm_num [Fin.sum_univ_succ,Nat.reduceAdd] at f1 f2 f3
  have a0:a 0=(-4/35)*a 3-(3/14)*a 4:=by linear_combination 72*f1-240*f2+180*f3
  have a1:a 1=(6/7)*a 3+(10/7)*a 4:=by linear_combination -240*f1+900*f2-720*f3
  have a2:a 2=(-12/7)*a 3-(15/7)*a 4:=by linear_combination 180*f1-720*f2+600*f3
  let t:=v/u
  have uv:u*t=v:=by dsimp [t];rw [mul_comm,div_mul_cancel₀ _ un]
  have t0:t≠0:=div_ne_zero vn un
  have t1:t-1≠0:=by
    intro he
    have ht:t=1:=sub_eq_zero.mp he
    apply vu
    rw [←uv,ht,mul_one]
  have aft (k:ℕ) (h:paidMoment ((X-C u)*P) v k=0) :
      (∑ j:Fin 5,a j*t^j.val*(t/((k+j.val+2:ℕ):K)-1/((k+j.val+1:ℕ):K)))=0:=by
    have clean:
        paidMoment ((X-C u)*P) v k=v^(k+1)*u*
          (∑ j:Fin 5,a j*t^j.val*(t/((k+j.val+2:ℕ):K)-1/((k+j.val+1:ℕ):K))) := by
      rw [paid_affine,←uv,expand,expand,Finset.mul_sum,Finset.mul_sum,Finset.mul_sum,
        ←Finset.sum_sub_distrib,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [show k+1+j.val+1=k+j.val+2 by omega,pow_succ (u*t) (k+1)]
      simp only [div_eq_mul_inv]
      ring
    rw [h] at clean
    exact (mul_eq_zero.mp clean.symm).resolve_left (mul_ne_zero (pow_ne_zero _ vn) un)
  have g1:=aft 1 g₁
  have g2:=aft 2 g₂
  norm_num [Fin.sum_univ_succ,Nat.reduceAdd] at g1 g2
  rw [a0,a1,a2] at g1 g2
  let c11:K:=(t-1)^2*(5*t-2)*(7*t-6)/210
  let c12:K:=(t-1)^2*(12*t^3+10*t^2-28*t+9)/84
  let c21:K:=(t-1)^2*(30*t^2-35*t+8)/210
  let c22:K:=(t-1)^2*(7*t^3+6*t^2-15*t+4)/56
  have l1:c11*a 3+c12*a 4=0:=by dsimp only [c11,c12];linear_combination g1
  have l2:c21*a 3+c22*a 4=0:=by dsimp only [c21,c22];linear_combination g2
  have factor:c11*c22-c12*c21=t*(t-1)^6*(15*t^2-24*t+10)/35280:=by
    dsimp only [c11,c12,c21,c22];ring
  have nq:15*t^2-24*t+10≠0:=by
    intro e
    apply fixed_ratio_ne un vn ur vr
    rw [←uv]
    linear_combination u^2*e
  have d:c11*c22-c12*c21≠0:=by
    rw [factor]
    exact div_ne_zero (mul_ne_zero (mul_ne_zero t0 (pow_ne_zero _ t1)) nq) (by norm_num)
  have d3:(c11*c22-c12*c21)*a 3=0:=by linear_combination c22*l1-c12*l2
  have d4:(c11*c22-c12*c21)*a 4=0:=by linear_combination c11*l2-c21*l1
  have z3: a 3=0:=(mul_eq_zero.mp d3).resolve_left d
  have z4: a 4=0:=(mul_eq_zero.mp d4).resolve_left d
  have az (j:Fin 5):a j=0:=by
    fin_cases j
    · change a 0=0
      simpa only [z3,z4,mul_zero,sub_zero] using a0
    · change a 1=0
      simpa only [z3,z4,mul_zero,add_zero] using a1
    · change a 2=0
      simpa only [z3,z4,mul_zero,sub_zero] using a2
    · exact z3
    · exact z4
  apply pn
  ext k
  rw [coeff_zero]
  by_cases h:k<5
  · exact (mul_eq_zero.mp (az ⟨k,h⟩)).resolve_right (pow_ne_zero _ un)
  · exact coeff_eq_zero_of_natDegree_lt (by omega)
end RKCert.Paired.EarlyFifteen
