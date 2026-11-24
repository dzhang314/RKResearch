module

public import RKCert.ReviewedNative.OneOffSources

@[expose] public section

/-! # Exact source compatibility, common to the two amplitude closures -/
namespace RKResearch.Certified.Graded.OneOff
open scoped Classical Matrix
variable {K : Type*} [Field K] [CharZero K] {s : ℕ}
variable {A : Matrix (Fin s) (Fin s) K}

abbrev rowM1 (x G : K) := x^2/2+G
abbrev rowM2 (a lam x G H : K) := x^3/3+(2*a/3)*G+lam*H
abbrev rowM3 (a mu nu x G H Z : K) := x^4/4+(a^2/2)*G+mu*H+nu*Z

def Btwo (a d x : K) : K := 3*x^2-4*(a+d)*x+6*a*d

def Qres (a d lam mu nu x G H Z : K) : K :=
  (a+d)*rowM2 a lam x G H-a*d*rowM1 x G-rowM3 a mu nu x G H Z

def Hres (a d hd gam lam kap x G H Z : K) : K :=
  (hd/d)*(rowM2 a lam x G H-a*rowM1 x G)/(d-a)+
    gam*(H-(baseAmp a/a)*(d*rowM1 x G-rowM2 a lam x G H)/(d-a))-kap*Z

theorem qres_of_four_sources (ha : ∀ i j, i ≤ j → A i j = 0) {a d hd v gam lam mu nu : K}
    {Z : Fin s → K} (i : Fin s)
    (Q2 : mDef A 2=(2*a/3) • g A+lam • h A)
    (Q3 : mDef A 3=((a^2/2) • g A+mu • h A)+nu • Z)
    (pre : ∀ j, j < i → FourFeatures a d hd v gam (nodes A j) (g A j) (h A j)) :
    Qres a d lam mu nu (nodes A i) (g A i) (h A i) (Z i)=0 := by
  unfold Qres rowM1 rowM2 rowM3
  have e := three_sources_cubic ha a d i (fun j hj=>four_features_clocks (pre j hj))
  rw [←m2_relation Q2 i,←m1_relation A i,←m3_relation Q3 i,←e,sub_self]

theorem hres_of_four_sources (ha : ∀ i j, i ≤ j → A i j = 0) {a d hd v gam lam kap : K}
    {Z : Fin s → K} (i : Fin s) (an : a≠0) (dn : d≠0) (da : d≠a)
    (Q2 : mDef A 2=(2*a/3) • g A+lam • h A) (Krow : k A=kap • Z)
    (pre : ∀ j, j < i → FourFeatures a d hd v gam (nodes A j) (g A j) (h A j)) :
    Hres a d hd gam lam kap (nodes A i) (g A i) (h A i) (Z i)=0 := by
  unfold Hres rowM1 rowM2
  rw [←m2_relation Q2 i,←m1_relation A i]
  have e := four_sources_h_action ha i an dn da pre
  have kw : k A i=kap*Z i := congrFun Krow i
  rw [←kw,←e,sub_self]

theorem qres_clean (a d lam mu nu x : K) :
    Qres a d lam mu nu x 0 0 0= -x^2*Btwo a d x/12 := by
  unfold Qres Btwo
  ring

end RKResearch.Certified.Graded.OneOff
