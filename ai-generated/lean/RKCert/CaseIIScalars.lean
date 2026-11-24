module

public import RKCert.GradedOperators
public import Mathlib.Tactic.LinearCombination

@[expose] public section
/-! # Scalar elimination at the first five rows of the evanescent-clock case -/
namespace RKCert.Paired.CaseII
variable {K : Type*} [Field K] [CharZero K]

/-- The convenient denominator-cleared quartic and its formal derivative. -/
def Q (t y x : K) : K := x^2*(x-y)*(2*x-3*t)
def DQ (t y x : K) : K := 8*x^3-(9*t+6*y)*x^2+6*t*y*x

/-- Consequences of the first three rows, with the second physical node normalized to one. -/
theorem third_row (t a d w : K) (hd : d=a-t^2/2) (hw : w= -a/2)
    (hs : d=0 ∨ t=1 ∧ d= -(1/2:K))
    (h0 : t=0 → d=0 → w=0 → False) (h1 : t=1 → d= -(1/2:K) → w=0 → False) :
    d=0 ∧ t≠0 ∧ a=t^2/2 ∧ w= -(t^2)/4 := by
  have hx : d=0 := by
    rcases hs with h|⟨ht,h⟩
    · exact h
    · exfalso; apply h1 ht h
      rw [ht,h] at hd
      linear_combination hw + (1/2:K)*hd
  have ha : a=t^2/2 := by linear_combination -hd + hx
  have hw' : w= -(t^2)/4 := by rw [hw,ha]; ring
  exact ⟨hx,fun ht => h0 ht hx (by simp [hw',ht]),ha,hw'⟩

/-- Calibration of the universal cubic primitive row on the first two nonzero rows. -/
theorem cubic_calibration (t a u v : K) (ht : t≠0) (ha : a=t^2/2)
    (h1 : -1=u*(-(1/2:K))) (h2 : 3*a-t^3=v*(-(t^2)/4)) : u=2 ∧ v=4*t-6 := by
  constructor
  · linear_combination 2*h1
  · apply mul_left_cancel₀ (pow_ne_zero 2 ht)
    rw [ha] at h2
    linear_combination 4*h2

/-- Solve the two paid elementary moment equations without dividing by any new node. -/
theorem row_solve (t z a e d : K) (_ht : t≠0)
    (h2 : d=a+t*e-z^2/2)
    (h3 : 3*(a+t^2*e)-z^3 = 2*d+(4*t-6)*(-a/2)) :
    2*t*a=z^2*(3*t-2*z)+2*d*(3*t-2) ∧
    t^2*e=z^2*(z-t)+2*d*(1-t) := by
  constructor
  · linear_combination -6*t*h2 - 2*h3
  · linear_combination (2*t)*h2 + h3

/-- The fourth physical node is regular, distinct from zero and the third one. -/
theorem fourth_row (t z a e d w : K) (ht : t≠0)
    (h2 : d=a+t*e-z^2/2) (hw : w= -a/2)
    (h3 : 3*(a+t^2*e)-z^3 = 2*d+(4*t-6)*w)
    (hs : d=0 ∨ z=1 ∧ d= -(1/2:K))
    (h0 : z=0 → d=0 → w=0 → False) (h1 : z=1 → d= -(1/2:K) → w=0 → False)
    (hT : z=t → d=0 → w= -(t^2)/4 → False) :
    d=0 ∧ z≠0 ∧ z≠t ∧ 2*t*a=z^2*(3*t-2*z) ∧ t^2*e=z^2*(z-t) := by
  obtain ⟨hA,hE⟩ := row_solve t z a e d ht h2 (hw ▸ h3)
  have d0 : d=0 := by
    rcases hs with h|⟨hz,h⟩
    · exact h
    · exfalso; apply h1 hz h
      rw [hz,h] at hA
      apply mul_left_cancel₀ ht
      linear_combination t*hw - hA/4
  rw [d0] at hA hE
  simp only [mul_zero,zero_mul,add_zero] at hA hE
  refine ⟨d0,?_,?_,hA,hE⟩
  · intro hh; apply h0 hh d0
    rw [hh] at hA
    apply mul_left_cancel₀ ht
    linear_combination t*hw - hA/4
  · intro hh; apply hT hh d0
    rw [hh] at hA
    apply mul_left_cancel₀ ht
    linear_combination t*hw - hA/4


/-- A regular fourth-type row acted on by the cubic clock transport. -/
theorem tap_calibration (t z a e w k : K) (_ht : t≠0) (hz : z≠0) (hzt : z≠t)
    (hA : 2*t*a=z^2*(3*t-2*z)) (hE : t^2*e=z^2*(z-t)) (hw : w= -a/2)
    (hT : e*(-(t^2)/4)=k*(z-t)*w) :
    w≠0 ∧ 4*t*w= -(z^2)*(3*t-2*z) ∧ k*(3*t-2*z)=t := by
  have hW : 4*t*w= -(z^2)*(3*t-2*z) := by linear_combination 4*t*hw - hA
  have hK : 4*k*w= -(z^2) := by
    apply mul_left_cancel₀ (sub_ne_zero.mpr hzt)
    linear_combination -4*hT-hE
  have hw0 : w≠0 := by
    intro h; rw [h,mul_zero] at hK
    exact (neg_ne_zero.mpr (pow_ne_zero 2 hz)) hK.symm
  refine ⟨hw0,hW,?_⟩
  apply mul_left_cancel₀ (pow_ne_zero 2 hz)
  linear_combination k*hW - t*hK

/-- The quartic annihilation detects exactly the incoming fourth-stage tap or equal-node alternative. -/
theorem terminal_tap_or_repeat (t z y k u v w W a e f m n : K)
    (ht : t≠0) (hz : z≠0) (hzt : z≠t) (hw : w≠0)
    (hW : 4*t*w= -(z^2)*(3*t-2*z))
    (hAZ : e*(-(t^2)/4)=k*(z-t)*w)
    (hAY : m*(-(t^2)/4)+n*w=k*(y-t)*W)
    (ha : a= -2*w) (hf : f= -2*W)
    (hT : (t^2/2)*DQ t y 1-Q t y t = (u+v*t)*(-(t^2)/4))
    (hZ : a*DQ t y 1+e*DQ t y t-Q t y z = (u+v*z)*w)
    (hY : f*DQ t y 1+m*DQ t y t+n*DQ t y z = (u+v*y)*W) :
    n=0 ∨ y=z := by
  let wT := -(t^2)/4
  have hn : wT≠0 := div_ne_zero (neg_ne_zero.mpr (pow_ne_zero 2 ht)) (by norm_num)
  have hdT : DQ t y t=4*t*wT := by unfold DQ wT; ring
  have hqT : Q t y t=4*t*(t-y)*wT := by unfold Q wT; ring
  have hqZ : Q t y z=4*t*(z-y)*w := by unfold Q; linear_combination -(z-y)*hW
  have hdZ : DQ t y z-4*t*w=6*z*(z-t)*(z-y) := by unfold DQ; linear_combination -hW
  have hvT : u+v*t = -2*DQ t y 1 + 4*t*(y-t) := by
    apply mul_right_cancel₀ hn
    change t^2/2*DQ t y 1-Q t y t=(u+v*t)*wT at hT
    rw [hqT] at hT
    dsimp [wT] at *
    linear_combination -hT
  have hvZ : u+v*z = -2*DQ t y 1 +4*t*k*(z-t)+4*t*(y-z) := by
    apply mul_right_cancel₀ hw
    rw [ha,hdT,hqZ] at hZ
    change e*wT=k*(z-t)*w at hAZ
    linear_combination -hZ+4*t*hAZ
  have hvY : u+v*y = -2*DQ t y 1 +4*t*k*(y-t) := by
    apply mul_left_cancel₀ (sub_ne_zero.mpr hzt)
    linear_combination (y-t)*hvZ + (z-y)*hvT
  have hP : n*(DQ t y z-4*t*w)=0 := by
    rw [hf,hdT,hvY] at hY
    change m*wT+n*w=k*(y-t)*W at hAY
    linear_combination hY-4*t*hAY
  rw [hdZ] at hP
  rcases mul_eq_zero.mp hP with h|h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left
      (mul_ne_zero (mul_ne_zero (by norm_num) hz) (sub_ne_zero.mpr hzt)))).symm

/-- With no new tap the fifth row repeats one of the previous moment profiles. -/
theorem no_zero_tap (t z y k wz W f m d : K) (ht : t≠0)
    (hzW : 4*t*wz= -(z^2)*(3*t-2*z)) (hk : k*(3*t-2*z)=t)
    (h2 : d=f+t*m-y^2/2) (hW : W= -f/2)
    (h3 : 3*(f+t^2*m)-y^3=2*d+(4*t-6)*W) (hT : m*(-(t^2)/4)=k*(y-t)*W)
    (hs : d=0 ∨ y=1 ∧ d= -(1/2:K))
    (h0 : y=0 → d=0 → W=0 → False) (h1 : y=1 → d= -(1/2:K) → W=0 → False)
    (hT' : y=t → d=0 → W= -(t^2)/4 → False)
    (hZ : y=z → d=0 → W=wz → False) : False := by
  obtain ⟨hd,hy,hyt,ha,he⟩ := fourth_row t y f m d W ht h2 hW h3 hs h0 h1 hT'
  obtain ⟨_,hyW,hyK⟩ := tap_calibration t y f m W k ht hy hyt ha he hW hT
  have hk0 : k≠0 := by intro h; rw [h,zero_mul] at hk; exact ht hk.symm
  have hyz : y=z := by
    apply mul_left_cancel₀ hk0
    linear_combination (hk-hyK)/2
  apply hZ hyz hd
  rw [hyz] at hyW
  apply mul_left_cancel₀ (mul_ne_zero (by norm_num : (4:K)≠0) ht)
  linear_combination hyW-hzW

/-- A nonzero fourth tap at a repeated node contradicts closure under the next clock word. -/
theorem repeat_contradiction (t z k g w W e m n : K) (hzt : z≠t) (hw : w≠0) (hn : n≠0)
    (hA : e*(-(t^2)/4)=k*(z-t)*w)
    (hB : m*(-(t^2)/4)+n*w=k*(z-t)*W)
    (hC : e*(t*(-(t^2)/4))=g*w)
    (hD : m*(t*(-(t^2)/4))+n*(z*w)=g*W) : False := by
  apply (mul_ne_zero (mul_ne_zero hn (sub_ne_zero.mpr hzt)) (pow_ne_zero 2 hw))
  linear_combination w*hD-W*hC-t*w*hB+t*W*hA

end RKCert.Paired.CaseII
