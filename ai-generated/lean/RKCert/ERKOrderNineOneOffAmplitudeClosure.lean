module

public import RKCert.ERKOrderNineOneOffStructure
public import RKCert.ERKOrderNineOneOffCaseTwo
public import RKCert.ERKOrderNineOneOffCaseThree

@[expose] public section

/-! # Constant defect amplitude on the actual p8/p9 sole-off chart -/
namespace RKCert.Paired.OneOff
open Module Polynomial
open scoped Classical

variable {K : Type*} [Field K] [CharZero K] {s p : ℕ}
variable {A : Fin s→Fin s→K} {b : Vec K s}

/-- The global constant-amplitude chart, without assuming any numbered
positions for the first two feature events. -/
structure ConstantAmplitude (A : Fin s→Fin s→K) (a d : K) (i j : Fin s) : Prop where
  origin : Origin A a i
  node : nodes A j=d
  clean : g A j=0
  dn : d≠0
  hj : h A j=twoHd a d
  first_h : FirstH A a (twoLam a d) j
  amplitude : (g A)^2=baseAmp a • g A
  span_three : zeroSpace A 3=twoSpan (g A) (h A)
  q2 : mDef A 2=(2*a/3) • g A+twoLam a d • h A

theorem constant_amplitude_of_single_off (ha : StrictLower A)
    (ho : HasTreeOrderAtLeast A b p) (hN : (supportedNodes A (g A)).card=1)
    (hp : 8≤p) (hs : 0<s)
    (rank3 : finrank K (zeroSpace A 3)=2) (rank4 : finrank K (zeroSpace A 4)=3) :
    ∃ (a d : K) (i j : Fin s), ConstantAmplitude A a d i j := by
  obtain ⟨a,i,lam,j,case⟩ := one_off_amplitude_fork ha ho hN hp hs rank3 rank4
  rcases case.alternatives with ⟨amp,on⟩|⟨_,ind⟩
  · have e : nodes A j≠0 ∧ h A j=twoHd a (nodes A j) ∧ lam=twoLam a (nodes A j) := by
      rcases case.event.alternative with t|t
      · exact t.2
      · exact (t.1 on).elim
    obtain ⟨dn,hj,e⟩ := e
    subst lam
    exact ⟨a,nodes A j,i,j,⟨case.origin,rfl,on,dn,hj,case.event,amp,case.span_three,case.q2⟩⟩
  · have sep : Separated A 4 := explicit_separated ha ho hp hs
    by_cases on : g A j=0
    · exact (independent_square_on_first_impossible ha sep case.origin case.event case.q2 ind on).elim
    · exact (independent_square_off_first_impossible ha sep case.origin case.event case.q2 ind on).elim

theorem order9_constant_amplitude {A : Fin 12→Fin 12→K} {b : Vec K 12}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 9)
    (hN : (supportedNodes A (g A)).card=1) :
    ∃ (a d : K) (i j : Fin 12), ConstantAmplitude A a d i j := by
  obtain ⟨_,h3,h4,_⟩ := order9_twelve_stage_chart ha ho
  exact constant_amplitude_of_single_off ha ho hN (by decide) (by decide) h3 h4

theorem order8_constant_amplitude {A : Fin 10→Fin 10→K} {b : Vec K 10}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 8)
    (hN : (supportedNodes A (g A)).card=1) :
    ∃ (a d : K) (i j : Fin 10), ConstantAmplitude A a d i j := by
  obtain ⟨_,_,_,_,_,h3,h4,_⟩ := order8_ten_stage_chart ha ho
  exact constant_amplitude_of_single_off ha ho hN (by decide) (by decide) h3 h4

/-- The off-clock cancellation is on aggregate output weight, not on
any individual output coefficient or the sum over an on copy. -/
theorem single_off_weight_cancel {a d : K} {i j : Fin s}
    (D : ConstantAmplitude A a d i j) (ho : HasTreeOrderAtLeast A b p)
    (hN : (supportedNodes A (g A)).card=1) (hp : 3≤p) :
    ∀ x∈supportedNodes A (g A), offWeight A b x=0 := by
  apply offWeight_eq_zero_from_head ho (C (baseAmp a))
  · intro l off
    simpa only [eval_C] using (amplitude_value D.amplitude off).symm
  · change (supportedNodes A (g A)).card+2≤p
    omega

end RKCert.Paired.OneOff
