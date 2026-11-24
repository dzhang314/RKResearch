module
public import RKCert.OrderTwelveArithmetic
@[expose] public section

/-! # The pure-factor p12 gate over arbitrary characteristic-zero fields
The factor submitted by a downstream proof is constrained by the complete factor
identity, not a selected modular ordering. A common leading scalar 132 has
been retained to keep the product identities integral. -/
namespace RKCert.OrderTwelve
variable {K : Type*} [Field K] [CharZero K]
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000

def evalFour (q0 q1 q2 q3 q4 x : K) : K :=
  q0+q1*x+q2*x^2+q3*x^3+q4*x^4

def pureMoment (q0 q1 q2 q3 q4 x : K) : K :=
  q0*x^2/2+q1*x^3/3+q2*x^4/4+q3*x^5/5+q4*x^6/6

/-- Excludes every normalized quartic factor and every eligible endpoint, simultaneously. -/
theorem quartic_actual_factor_gate (u w q0 q1 q2 q3 q4 : K)
    (fit : ∀ x : K, dFive x=(x-u)*evalFour q0 q1 q2 q3 q4 x)
    (hw : w=1 ∨ w=u) : pureMoment q0 q1 q2 q3 q4 w ≠0 := by
  have hu : dFive u=0 := by simpa using fit u
  have e0 := fit 0
  have e1 := fit 1
  have e2 := fit 2
  have e3 := fit 3
  have e4 := fit 4
  have e5 := fit 5
  simp only [dFive,evalFour] at e0 e1 e2 e3 e4 e5
  have h4 : q4=132 := by
    linear_combination ((1/120))*e0 + (-(1/24))*e1 + ((1/12))*e2 + (-(1/12))*e3 + ((1/24))*e4 + (-(1/120))*e5
  have h3 : q3=132*u - 330 := by
    linear_combination (((1/120))*(u - 15))*e0 + ((-(1/24))*(u - 14))*e1 + (((1/12))*(u - 13))*e2 + ((-(1/12))*(u - 12))*e3 + (((1/24))*(u - 11))*e4 + ((-(1/120))*(u - 10))*e5
  have h2 : q2=132*u^2 - 330*u + 300 := by
    linear_combination (((1/120))*(u^2 - 15*u + 85))*e0 + ((-(1/24))*(u^2 - 14*u + 71))*e1 + (((1/12))*(u^2 - 13*u + 59))*e2 + ((-(1/12))*(u^2 - 12*u + 49))*e3 + (((1/24))*(u^2 - 11*u + 41))*e4 + ((-(1/120))*(u^2 - 10*u + 35))*e5
  have h1 : q1=132*u^3 - 330*u^2 + 300*u - 120 := by
    linear_combination (((1/120))*(u^3 - 15*u^2 + 85*u - 225))*e0 + ((-(1/24))*(u - 7)*(u^2 - 7*u + 22))*e1 + (((1/12))*(u^3 - 13*u^2 + 59*u - 107))*e2 + ((-(1/12))*(u - 6)*(u^2 - 6*u + 13))*e3 + (((1/24))*(u^3 - 11*u^2 + 41*u - 61))*e4 + ((-(1/120))*(u - 5)*(u^2 - 5*u + 10))*e5
  have h0 : q0=132*u^4 - 330*u^3 + 300*u^2 - 120*u + 20 := by
    linear_combination (((1/120))*(u^4 - 15*u^3 + 85*u^2 - 225*u + 274))*e0 + ((-(1/24))*(u - 5)*(u - 4)*(u - 3)*(u - 2))*e1 + (((1/12))*(u - 1)*(u - 5)*(u - 4)*(u - 3))*e2 + ((-(1/12))*(u - 1)*(u - 5)*(u - 4)*(u - 2))*e3 + (((1/24))*(u - 1)*(u - 5)*(u - 3)*(u - 2))*e4 + ((-(1/120))*(u - 1)*(u - 4)*(u - 3)*(u - 2))*e5
  rw [h0,h1,h2,h3,h4]
  rcases hw with hw|hw
  · rw [hw]
    apply ne_of_eq_of_ne _ (quarticAtOne_gate u hu)
    unfold pureMoment quarticAtOneMoment
    ring
  · rw [hw]
    apply ne_of_eq_of_ne _ (quarticAtRoot_gate u hu)
    unfold pureMoment quarticAtRootMoment
    ring

/-- Excludes every normalized cubic factor and every eligible endpoint, simultaneously. -/
theorem cubic_actual_factor_gate (u a w q0 q1 q2 q3 : K)
    (hne : a≠u)
    (fit : ∀ x : K, dFive x=(x-u)*(x-a)*evalFour q0 q1 q2 q3 0 x)
    (hw : w=1 ∨ w=u ∨ w=a) : pureMoment q0 q1 q2 q3 0 w ≠0 := by
  have hu : dFive u=0 := by simpa using fit u
  have ha : dFive a=0 := by simpa using fit a
  have e0 := fit 0
  have e1 := fit 1
  have e2 := fit 2
  have e3 := fit 3
  have e4 := fit 4
  have e5 := fit 5
  simp only [dFive,evalFour] at e0 e1 e2 e3 e4 e5
  have h3 : q3=132 := by
    linear_combination ((1/120))*e0 + (-(1/24))*e1 + ((1/12))*e2 + (-(1/12))*e3 + ((1/24))*e4 + (-(1/120))*e5
  have h2 : q2=132*u + 132*a - 330 := by
    linear_combination (((1/120))*(u + a - 15))*e0 + ((-(1/24))*(u + a - 14))*e1 + (((1/12))*(u + a - 13))*e2 + ((-(1/12))*(u + a - 12))*e3 + (((1/24))*(u + a - 11))*e4 + ((-(1/120))*(u + a - 10))*e5
  have h1 : q1=132*u^2 + 132*u*a - 330*u + 132*a^2 - 330*a + 300 := by
    linear_combination (((1/120))*(u^2 + u*a - 15*u + a^2 - 15*a + 85))*e0 + ((-(1/24))*(u^2 + u*a - 14*u + a^2 - 14*a + 71))*e1 + (((1/12))*(u^2 + u*a - 13*u + a^2 - 13*a + 59))*e2 + ((-(1/12))*(u^2 + u*a - 12*u + a^2 - 12*a + 49))*e3 + (((1/24))*(u^2 + u*a - 11*u + a^2 - 11*a + 41))*e4 + ((-(1/120))*(u^2 + u*a - 10*u + a^2 - 10*a + 35))*e5
  have h0 : q0=132*u^3 + 132*u^2*a - 330*u^2 + 132*u*a^2 - 330*u*a + 300*u + 132*a^3 - 330*a^2 + 300*a - 120 := by
    linear_combination (((1/120))*(u^3 + u^2*a - 15*u^2 + u*a^2 - 15*u*a + 85*u + a^3 - 15*a^2 + 85*a - 225))*e0 + ((-(1/24))*(u + a - 7)*(u^2 - 7*u + a^2 - 7*a + 22))*e1 + (((1/12))*(u^3 + u^2*a - 13*u^2 + u*a^2 - 13*u*a + 59*u + a^3 - 13*a^2 + 59*a - 107))*e2 + ((-(1/12))*(u + a - 6)*(u^2 - 6*u + a^2 - 6*a + 13))*e3 + (((1/24))*(u^3 + u^2*a - 11*u^2 + u*a^2 - 11*u*a + 41*u + a^3 - 11*a^2 + 41*a - 61))*e4 + ((-(1/120))*(u + a - 5)*(u^2 - 5*u + a^2 - 5*a + 10))*e5
  rw [h0,h1,h2,h3]
  rcases hw with hw|hw|hw
  · rw [hw]
    apply ne_of_eq_of_ne _ (cubicAtOne_gate u a hu ha hne)
    unfold pureMoment cubicAtOneMoment
    ring
  · rw [hw]
    apply ne_of_eq_of_ne _ (cubicAtRoot_gate u a hu ha hne)
    unfold pureMoment cubicAtRootMoment
    ring
  · rw [hw]
    apply ne_of_eq_of_ne _ (cubicAtRoot_gate a u ha hu hne.symm)
    unfold pureMoment cubicAtRootMoment
    ring

end RKCert.OrderTwelve
