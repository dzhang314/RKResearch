module
public import RKCert.ReviewedNative.OrderNineSixOnOnEighth

@[expose] public section

/-! # Native on-eighth motion forces the checked terminal Hankel scalar to vanish -/
namespace RKResearch.Certified.Graded.MultiOff
open RKResearch Module Polynomial OneOff Reverse RKCert.Endpoint
open scoped Matrix Classical
variable {K : Type*} [Field K] 

variable [LinearOrder K] [IsStrictOrderedRing K]
theorem order9_actual_five_six_on_eighth_atlas
    {A : Fin 12→Fin 12→K} {b : (Fin 12→K)}
    (ha : ∀i j,i≤j → A i j=0) (ho : HasOrder 9 A b)
    (N : (offKnots A).card=5) (M : (cleanKnots A).card=6)
    (hF : zeroSpace A 4=band A 2)
    {P : K[X]} (dP : P.natDegree≤2)
    (fit : ∀i,g A i≠0 → P.eval (nodes A i)=g A i)
    (fg : ActualSixOnFG A P) (on : g A (lowPrefix10 (7:Fin 10))=0) :
    RKCert.Paired.sixOnHc (nodes A (lowPrefix10 fg.first)) (nodes A (lowPrefix10 (8:Fin 10)))
      (nodes A (lowPrefix10 (Fin.last 9)))=0 := by
  let h := nodes A (lowPrefix10 fg.first)
  let u := nodes A (lowPrefix10 (8:Fin 10))
  let v := nodes A (lowPrefix10 (Fin.last 9))
  let a := fg.head_scale
  let t := fg.affine_parameter
  let R := RKCert.Paired.sixOnNormalizedCollisionPoly h t
  let m (k : ℕ) := (RKCert.Paired.primitive ((1-X)^k*R)).eval 1
  have hh := order9_actual_five_six_on_eighth_hankel ha ho N M hF dP fit fg on
  simp_rw [←scalar_primitive] at hh
  have r := RKCert.Paired.sixOnCollisionPoly_scale fg.head_shape
  change fiveSixCollisionPoly P h=C a*R at r
  have mr (k : ℕ) : (RKCert.Paired.primitive ((1-X)^k*fiveSixCollisionPoly P h)).eval 1=a*m k := by
    rw [r]
    have e : (1-X)^k*(C a*R)=C a*((1-X)^k*R) := by ring
    rw [e,←smul_eq_C_mul,map_smul,smul_eq_C_mul,eval_mul,eval_C]
  change (RKCert.Paired.primitive ((1-X)^2*fiveSixCollisionPoly P h)).eval 1*
    (RKCert.Paired.primitive ((1-X)^4*fiveSixCollisionPoly P h)).eval 1-
      ((RKCert.Paired.primitive ((1-X)^3*fiveSixCollisionPoly P h)).eval 1)^2=0 at hh
  rw [mr,mr,mr] at hh
  have hz : a^2*(m 2*m 4-(m 3)^2)=0 := by linear_combination hh
  have hn := (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ fg.head_scale_nonzero)
  have he := RKCert.Paired.sixOnCollision_coeffs h t
  change 1058400*(m 2*m 4-(m 3)^2)=_ at he
  rw [hn,mul_zero] at he
  let F0 := RKCert.Paired.sixOnF u v (RKCert.Paired.fixedRadauP0 h)
  let F1 := RKCert.Paired.sixOnF u v (RKCert.Paired.fixedRadauP1 h)
  have eF : F0= -t*F1 := by
    have ef := fg.F_zero
    change RKCert.Paired.sixOnF u v (fun x=>RKCert.Paired.fixedRadauP0 h x+t*RKCert.Paired.fixedRadauP1 h x)=0 at ef
    dsimp only [F0,F1]
    unfold RKCert.Paired.sixOnF at ef ⊢
    linear_combination ef
  change RKCert.Paired.sixOnCollisionA2 h*F0^2-RKCert.Paired.sixOnCollisionA1 h*F0*F1+RKCert.Paired.sixOnCollisionA0 h*F1^2=0
  rw [eF]
  linear_combination -F1^2*he
end RKResearch.Certified.Graded.MultiOff
