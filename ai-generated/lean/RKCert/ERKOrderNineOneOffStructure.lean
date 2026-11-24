module

public import RKCert.ERKOrderNineOneOffIndependentSquare
public import RKCert.ERKOrderNineOneOffAmplitudeCaseI
public import RKCert.ERKOrderNineOneOffJacobi
public import RKCert.ERKOrderNineOneOffTailCubic
public import RKCert.ERKOrderNineCausalInterpolation

@[expose] public section

/-! # Checked initial and terminal one-off reductions

The two independent-square branch closures and the physical derivation
of the middle prefix and tail are not asserted here. -/
namespace RKCert.Paired.OneOff
open Module

variable {K : Type*} [Field K] [CharZero K] {s p : ℕ}
variable {A : Fin s → Fin s → K} {b : Vec K s}

/-- A common physical fork at the first innovation, before constant
amplitude is established in the two independent-square cases. -/
structure AmplitudeFork (A : Fin s → Fin s → K) (a lam : K) (i j : Fin s) : Prop where
  origin : Origin A a i
  span_three : zeroSpace A 3=twoSpan (g A) (h A)
  q2 : mDef A 2=(2*a/3) • g A+lam • h A
  event : FirstH A a lam j
  alternatives :
    ((g A)^2=(-a^2/2) • g A ∧ g A j=0) ∨
    ((g A)^2∉zeroSpace A 3 ∧ IndependentShape A a lam i j)

omit [CharZero K] in
/-- The globally constant amplitude fixes each nonzero defect value. -/
theorem amplitude_value {a : K} (eq : (g A)^2=(-a^2/2) • g A)
    {i : Fin s} (hn : g A i≠0) : g A i= -a^2/2 := by
  have e := congrFun eq i
  simp only [Pi.pow_apply,Pi.smul_apply,smul_eq_mul] at e
  apply mul_right_cancel₀ hn
  simpa only [pow_two] using e

theorem one_off_amplitude_fork (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b p)
    (hN : (supportedNodes A (g A)).card=1) (hp : 8≤p) (hs : 0<s)
    (rank3 : finrank K (zeroSpace A 3)=2) (rank4 : finrank K (zeroSpace A 4)=3) :
    ∃ (a : K) (i : Fin s) (lam : K) (j : Fin s), AmplitudeFork A a lam i j := by
  obtain ⟨a,i,lam,j,O,e3,q2,F⟩ := first_h_of_actual ha ho hN (by omega) hs rank3
  refine ⟨a,i,lam,j,⟨O,e3,q2,F,?_⟩⟩
  by_cases sq : (g A)^2∈zeroSpace A 3
  · have gC := constant_amplitude_of_dependent_square ha
      (explicit_separated ha ho hp hs) rank3 rank4 O e3 q2 F sq
    left
    refine ⟨gC,?_⟩
    rcases F.alternative with t|⟨hn,hne,_,_,_⟩
    · exact t.1
    · exact (hne (amplitude_value gC hn)).elim
  · exact Or.inr ⟨sq,independent_square_shape ha rank3 rank4 O F e3 sq⟩

theorem order9_amplitude_fork {A : Fin 12 → Fin 12 → K} {b : Vec K 12}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 9)
    (hN : (supportedNodes A (g A)).card=1) :
    ∃ (a : K) (i : Fin 12) (lam : K) (j : Fin 12), AmplitudeFork A a lam i j := by
  obtain ⟨_,h3,h4,_⟩ := order9_twelve_stage_chart ha ho
  exact one_off_amplitude_fork ha ho hN (by decide) (by decide) h3 h4

theorem order8_amplitude_fork {A : Fin 10 → Fin 10 → K} {b : Vec K 10}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 8)
    (hN : (supportedNodes A (g A)).card=1) :
    ∃ (a : K) (i : Fin 10) (lam : K) (j : Fin 10), AmplitudeFork A a lam i j := by
  obtain ⟨_,_,_,_,_,h3,h4,_⟩ := order8_ten_stage_chart ha ho
  exact one_off_amplitude_fork ha ho hN (by decide) (by decide) h3 h4

end RKCert.Paired.OneOff
