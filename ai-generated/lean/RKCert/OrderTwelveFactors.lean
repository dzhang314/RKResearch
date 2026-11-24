module
public import RKCert.OrderTwelvePure

@[expose] public section
/-! # The pure-factor gates without a root-splitting assumption
At the virtual endpoint one the complementary quadratic need not split over
the coefficient field. This module uses its symmetric coefficients directly;
the other endpoints supply their own complementary root. -/
namespace RKCert.OrderTwelve
variable {K : Type*} [Field K] [CharZero K]
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768

private theorem dFive_no_double (u q0 q1 q2 q3 : K)
    (fit : ∀x : K, dFive x=(x-u)^2*evalFour q0 q1 q2 q3 0 x) : False := by
  have hu : dFive u=0 := by simpa using fit u
  unfold dFive at hu
  have e0 := fit 0
  have e1 := fit 1
  have e2 := fit 2
  have e3 := fit 3
  have e4 := fit 4
  have e5 := fit 5
  simp only [dFive,evalFour] at e0 e1 e2 e3 e4 e5
  have hd : 660*u^4 - 1320*u^3 + 900*u^2 - 240*u + 20=0 := by
    linear_combination ( - (1/24)*u^4 + (1/2)*u^3 - (17/8)*u^2 + (15/4)*u - (137/60))*e0 + ((5/24)*u^4 - (7/3)*u^3 + (71/8)*u^2 - (77/6)*u + 5)*e1 + ( - (5/12)*u^4 + (13/3)*u^3 - (59/4)*u^2 + (107/6)*u - 5)*e2 + ((5/12)*u^4 - 4*u^3 + (49/4)*u^2 - 13*u + (10/3))*e3 + ( - (5/24)*u^4 + (11/6)*u^3 - (41/8)*u^2 + (61/12)*u - (5/4))*e4 + ((1/24)*u^4 - (1/3)*u^3 + (7/8)*u^2 - (5/6)*u + (1/5))*e5
  apply (one_ne_zero : (1:K)≠0)
  linear_combination ( - 924*u^3 + 1386*u^2 - 600*u + 69)*hu + ((924/5)*u^4 - (1848/5)*u^3 + (1209/5)*u^2 - 57*u + (7/2))*hd

/-- Fourth-degree factor: w may just be specified to be an eligible knot off its support. -/
theorem quartic_off_factor (r w q0 q1 q2 q3 q4 : K)
    (fit : ∀x : K, dFive x=(x-r)*evalFour q0 q1 q2 q3 q4 x)
    (hw : w=1 ∨ dFive w=0 ∧ evalFour q0 q1 q2 q3 q4 w≠0) :
    pureMoment q0 q1 q2 q3 q4 w≠0 := by
  apply quartic_actual_factor_gate r w q0 q1 q2 q3 q4 fit
  rcases hw with h|⟨h,hp⟩
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp ((mul_eq_zero.mp ((fit w).symm.trans h)).resolve_right hp))

/-- Every cubic factor works over the original characteristic-zero field; its monic
quadratic complement need not split in that field. -/
theorem cubic_off_factor (s p w q0 q1 q2 q3 : K)
    (fit : ∀ x : K, dFive x=(x^2-s*x+p)*evalFour q0 q1 q2 q3 0 x)
    (hw : w=1 ∨ dFive w=0 ∧ evalFour q0 q1 q2 q3 0 w≠0) :
    pureMoment q0 q1 q2 q3 0 w≠0 := by
  rcases hw with h|⟨h,hp⟩
  · rw [h]
    intro hz
    have e0 := fit 0
    have e1 := fit 1
    have e2 := fit 2
    have e3 := fit 3
    have e4 := fit 4
    have e5 := fit 5
    simp only [dFive,evalFour] at e0 e1 e2 e3 e4 e5
    have hc0 : q0=132*s^3 - 330*s^2 - 264*s*p + 300*s + 330*p - 120 := by
      linear_combination ((1/120)*s^3 - (1/8)*s^2 - (1/60)*s*p + (17/24)*s + (1/8)*p - (15/8))*e0 + ( - (1/24)*s^3 + (7/12)*s^2 + (1/12)*s*p - (71/24)*s - (7/12)*p + (77/12))*e1 + ((1/12)*s^3 - (13/12)*s^2 - (1/6)*s*p + (59/12)*s + (13/12)*p - (107/12))*e2 + ( - (1/12)*s^3 + s^2 + (1/6)*s*p - (49/12)*s - p + (13/2))*e3 + ((1/24)*s^3 - (11/24)*s^2 - (1/12)*s*p + (41/24)*s + (11/24)*p - (61/24))*e4 + ( - (1/120)*s^3 + (1/12)*s^2 + (1/60)*s*p - (7/24)*s - (1/12)*p + (5/12))*e5
    have hc1 : q1=132*s^2 - 330*s - 132*p + 300 := by
      linear_combination ((1/120)*s^2 - (1/8)*s - (1/120)*p + (17/24))*e0 + ( - (1/24)*s^2 + (7/12)*s + (1/24)*p - (71/24))*e1 + ((1/12)*s^2 - (13/12)*s - (1/12)*p + (59/12))*e2 + ( - (1/12)*s^2 + s + (1/12)*p - (49/12))*e3 + ((1/24)*s^2 - (11/24)*s - (1/24)*p + (41/24))*e4 + ( - (1/120)*s^2 + (1/12)*s + (1/120)*p - (7/24))*e5
    have hc2 : q2=132*s - 330 := by
      linear_combination ((1/120)*s - (1/8))*e0 + ( - (1/24)*s + (7/12))*e1 + ((1/12)*s - (13/12))*e2 + ( - (1/12)*s + 1)*e3 + ((1/24)*s - (11/24))*e4 + ( - (1/120)*s + (1/12))*e5
    have hc3 : q3=132 := by
      linear_combination ((1/120))*e0 + ( - (1/24))*e1 + ((1/12))*e2 + ( - (1/12))*e3 + ((1/24))*e4 + ( - (1/120))*e5
    rw [hc0,hc1,hc2,hc3] at e0 e1 hz
    unfold pureMoment at hz
    have hr0 :  - 132*s^3*p + 330*s^2*p + 264*s*p^2 - 300*s*p - 330*p^2 + 120*p - 1=0 := by linear_combination e0
    have hr1 : 132*s^4 - 330*s^3 - 396*s^2*p + 300*s^2 + 660*s*p - 120*s + 132*p^2 - 300*p + 20=0 := by linear_combination e1-e0
    have hm : 66*s^3 - 121*s^2 - 132*s*p + 73*s + 121*p - (161/10)=0 := by linear_combination hz
    apply (one_ne_zero : (1:K)≠0)
    linear_combination ((131457546000/29324743)*s^3*p + (5148067320/4189249)*s^3 - (2904016698000/674469089)*s^2*p^2 - (7307940709080/674469089)*s^2*p - (1772128929780/674469089)*s^2 + (364495923000/674469089)*s*p^2 + (4742284875240/674469089)*s*p + (1258144516938/674469089)*s + (2904016698000/674469089)*p^3 + (2665823482080/674469089)*p^2 - (626582049960/674469089)*p - (304250048604/674469089))*hr0 + ((87638364000/29324743)*s^3*p + (3432044880/4189249)*s^3 - (1936011132000/674469089)*s^2*p^2 - (4703986941720/674469089)*s^2*p - (1135372684380/674469089)*s^2 + (81663021000/674469089)*s*p^2 + (2845112427300/674469089)*s*p + (764869591890/674469089)*s + (1936011132000/674469089)*p^3 + (1879394020020/674469089)*p^2 - (281526099102/674469089)*p - (173548635038/674469089))*hr1 + ( - (175276728000/29324743)*s^4*p - (6864089760/4189249)*s^4 + (9919069380000/674469089)*s^3*p^2 + (13753228056480/674469089)*s^3*p + (3007491003000/674469089)*s^3 - (5808033396000/674469089)*s^2*p^3 - (17360555636160/674469089)*s^2*p^2 - (15282500595120/674469089)*s^2*p - (2982173960100/674469089)*s^2 - (3143030418000/674469089)*s*p^3 + (244328408280/29324743)*s*p^2 + (6469607097000/674469089)*s*p + (1273515122520/674469089)*s + (5808033396000/674469089)*p^4 + (7912995140160/674469089)*p^3 + (1371006384840/674469089)*p^2 - (823230860100/674469089)*p - (196732740450/674469089))*hm
  · have hc := (mul_eq_zero.mp ((fit w).symm.trans h)).resolve_right hp
    let a := s-w
    have split (x : K) : x^2-s*x+p=(x-w)*(x-a) := by
      dsimp [a]
      linear_combination hc
    have hfit (x : K) : dFive x=(x-w)*(x-a)*evalFour q0 q1 q2 q3 0 x := by
      rw [fit,split]
    have hne : a≠w := by
      intro he
      apply dFive_no_double w q0 q1 q2 q3
      intro x; rw [hfit,he,pow_two]
    exact cubic_actual_factor_gate w a w q0 q1 q2 q3 hne hfit (Or.inr (Or.inl rfl))

end RKCert.OrderTwelve
