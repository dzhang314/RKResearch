module

public import RKCert.ERKOrderNineFiveSixOnPlacement

@[expose] public section

/-! # Exact scalar collision polynomial for the ordinary clean eighth stage -/
namespace RKCert.Paired
open Polynomial
variable {K : Type*} [Field K] [CharZero K]

noncomputable def sixOnNormalizedCollisionPoly (h t : K) : K[X] :=
  monomial 1 (3*h^3)+monomial 2 (3*h^2*(t-1))+
    monomial 3 (-h*(6+7*t))+monomial 4 (6+4*t)

theorem sixOnCollisionPoly_scale {h t a : K} {P : K[X]}
    (shape : ∀ x,P.eval x=a*(fixedRadauP0 h x+t*fixedRadauP1 h x)) :
    fiveSixCollisionPoly P h=C a*sixOnNormalizedCollisionPoly h t := by
  let _ : Infinite K := Infinite.of_injective (fun n : ℕ => (n:K)) Nat.cast_injective
  apply Polynomial.funext
  intro x
  simp [fiveSixCollisionPoly,sixOnNormalizedCollisionPoly,shape,fixedRadauP0,fixedRadauP1]
  ring

omit [CharZero K] in
private theorem mirrorPoly2 : (1-X:K[X])^2=
    monomial 0 1+monomial 1 (-2)+monomial 2 1 := by
  simp only [←C_mul_X_pow_eq_monomial,map_one,map_neg,map_ofNat,pow_zero,pow_one,mul_one,one_mul]
  ring

omit [CharZero K] in
private theorem mirrorPoly3 : (1-X:K[X])^3=
    monomial 0 1+monomial 1 (-3)+monomial 2 3+monomial 3 (-1) := by
  simp only [←C_mul_X_pow_eq_monomial,map_one,map_neg,map_ofNat,pow_zero,pow_one,mul_one,one_mul]
  ring

omit [CharZero K] in
private theorem mirrorPoly4 : (1-X:K[X])^4=
    monomial 0 1+monomial 1 (-4)+monomial 2 6+monomial 3 (-4)+monomial 4 1 := by
  simp only [←C_mul_X_pow_eq_monomial,map_one,map_neg,map_ofNat,pow_zero,pow_one,mul_one,one_mul]
  ring

theorem sixOnCollisionMoment2 (h t : K) :
    (primitive ((1-X)^2*sixOnNormalizedCollisionPoly h t)).eval 1 =
      (42*t*h^2-49*t*h+16*t+105*h^3-42*h^2-42*h+24)/420 := by
  rw [mirrorPoly2]
  simp only [sixOnNormalizedCollisionPoly,add_mul,mul_add,monomial_mul_monomial,map_add,
    eval_add,primitive_monomial,eval_monomial,one_pow,mul_one,Nat.reduceAdd,Nat.cast_ofNat]
  ring

theorem sixOnCollisionMoment3 (h t : K) :
    (primitive ((1-X)^3*sixOnNormalizedCollisionPoly h t)).eval 1 =
      (7*t*h^2-7*t*h+2*t+21*h^3-7*h^2-6*h+3)/140 := by
  rw [mirrorPoly3]
  simp only [sixOnNormalizedCollisionPoly,add_mul,mul_add,monomial_mul_monomial,map_add,
    eval_add,primitive_monomial,eval_monomial,one_pow,mul_one,Nat.reduceAdd,Nat.cast_ofNat]
  ring

theorem sixOnCollisionMoment4 (h t : K) :
    (primitive ((1-X)^4*sixOnNormalizedCollisionPoly h t)).eval 1 =
      (72*t*h^2-63*t*h+16*t+252*h^3-72*h^2-54*h+24)/2520 := by
  rw [mirrorPoly4]
  simp only [sixOnNormalizedCollisionPoly,add_mul,mul_add,monomial_mul_monomial,map_add,
    eval_add,primitive_monomial,eval_monomial,one_pow,mul_one,Nat.reduceAdd,Nat.cast_ofNat]
  ring

def sixOnCollisionA2 (h : K) : K := 378*h^4-882*h^3+753*h^2-280*h+40
def sixOnCollisionA1 (h : K) : K := 2268*h^5-3843*h^4+1302*h^3+912*h^2-660*h+120
def sixOnCollisionA0 (h : K) : K := 2646*h^6-2268*h^5-2268*h^4+2520*h^3-144*h^2-360*h+90

theorem sixOnCollision_coeffs (h t : K) :
    let e (k : ℕ) := (primitive ((1-X)^k*sixOnNormalizedCollisionPoly h t)).eval 1
    1058400*(e 2*e 4-(e 3)^2)=
      sixOnCollisionA2 h*t^2+sixOnCollisionA1 h*t+sixOnCollisionA0 h := by
  dsimp only
  rw [sixOnCollisionMoment2,sixOnCollisionMoment3,sixOnCollisionMoment4]
  unfold sixOnCollisionA2 sixOnCollisionA1 sixOnCollisionA0
  ring

noncomputable def sixOnHc (h u v : K) : K :=
  let F0 := sixOnF u v (fixedRadauP0 h)
  let F1 := sixOnF u v (fixedRadauP1 h)
  sixOnCollisionA2 h*F0^2-sixOnCollisionA1 h*F0*F1+sixOnCollisionA0 h*F1^2

section Ordered
variable {L : Type*} [Field L] [LinearOrder L] [IsStrictOrderedRing L]

/-- The actual on-eighth branch implies Hc=0 in the terminal atlas.
No affine coefficient, including F1, is divided out. -/
theorem order9_actual_five_six_on_eighth_atlas
    {A : Fin 12→Fin 12→L} {b : Vec L 12}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 9)
    (N : (supportedNodes A (qdef A)).card=5) (M : (onNodes A).card=6)
    (hF : zeroSpace A 4=chainSpan A (qdef A) 2)
    {P : L[X]} (dP : P.natDegree≤2)
    (fit : ∀i,qdef A i≠0 → P.eval (nodes A i)=qdef A i)
    (fg : ActualSixOnFG A P) (on : qdef A (lowPrefix10 (7:Fin 10))=0) :
    sixOnHc (nodes A (lowPrefix10 fg.first)) (nodes A (lowPrefix10 (8:Fin 10)))
      (nodes A (lowPrefix10 (Fin.last 9)))=0 := by
  let h := nodes A (lowPrefix10 fg.first)
  let u := nodes A (lowPrefix10 (8:Fin 10))
  let v := nodes A (lowPrefix10 (Fin.last 9))
  let a := fg.head_scale
  let t := fg.affine_parameter
  let R := sixOnNormalizedCollisionPoly h t
  let m (k : ℕ) := (primitive ((1-X)^k*R)).eval 1
  have hh := order9_actual_five_six_on_eighth_hankel ha ho N M hF dP fit fg on
  have r := sixOnCollisionPoly_scale fg.head_shape
  change fiveSixCollisionPoly P h=C a*R at r
  have mr (k : ℕ) : (primitive ((1-X)^k*fiveSixCollisionPoly P h)).eval 1=a*m k := by
    rw [r]
    have e : (1-X)^k*(C a*R)=C a*((1-X)^k*R) := by ring
    rw [e,←smul_eq_C_mul,map_smul,smul_eq_C_mul,eval_mul,eval_C]
  change (primitive ((1-X)^2*fiveSixCollisionPoly P h)).eval 1*
    (primitive ((1-X)^4*fiveSixCollisionPoly P h)).eval 1-
      ((primitive ((1-X)^3*fiveSixCollisionPoly P h)).eval 1)^2=0 at hh
  rw [mr,mr,mr] at hh
  have hz : a^2*(m 2*m 4-(m 3)^2)=0 := by linear_combination hh
  have hn := (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ fg.head_scale_nonzero)
  have he := sixOnCollision_coeffs h t
  change 1058400*(m 2*m 4-(m 3)^2)=_ at he
  rw [hn,mul_zero] at he
  let F0 := sixOnF u v (fixedRadauP0 h)
  let F1 := sixOnF u v (fixedRadauP1 h)
  have eF : F0= -t*F1 := by
    have ef := fg.F_zero
    change sixOnF u v (fun x=>fixedRadauP0 h x+t*fixedRadauP1 h x)=0 at ef
    dsimp only [F0,F1]
    unfold sixOnF at ef ⊢
    linear_combination ef
  change sixOnCollisionA2 h*F0^2-sixOnCollisionA1 h*F0*F1+sixOnCollisionA0 h*F1^2=0
  rw [eF]
  linear_combination -F1^2*he

end Ordered
end RKCert.Paired
