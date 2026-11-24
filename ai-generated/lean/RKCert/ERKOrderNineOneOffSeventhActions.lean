module

public import RKCert.ERKOrderNineOneOffSixth
public import RKCert.ERKOrderNineOneOffSeventhScalars

@[expose] public section

/-! # From the six physical source rows to the two seventh-row actions -/
namespace RKCert.Paired.OneOff.Seven
open Module Polynomial
open scoped Classical

variable {K : Type*} [Field K] [CharZero K] {A : Fin 12→Fin 12→K} {b : Vec K 12}

noncomputable def scaledH (A : Fin 12→Fin 12→K) (a : K) : Vec K 12 := a⁻¹ • h A

theorem scaledH_eval (a : K) (r : Fin 12) :
    scaledH A a r=h A r/a := by
  simp [scaledH,div_eq_mul_inv,mul_comm]

noncomputable def Jtest (A : Fin 12→Fin 12→K) (a : K) : Vec K 12 :=
  mat A (diag (nodes A) (scaledH A a))

noncomputable def Vtest (A : Fin 12→Fin 12→K) (a : K) : Vec K 12 :=
  mDef A 4+(2*a^2) • h A

theorem Jtest_mem (ho : HasTreeOrderAtLeast A b 9) (a : K) : Jtest A a∈zeroSpace A 5 := by
  unfold Jtest scaledH
  rw [map_smul,map_smul]
  exact (zeroSpace A 5).smul_mem _ (clockAg_mem ho)

theorem Vtest_mem (A : Fin 12→Fin 12→K) (a : K) : Vtest A a∈zeroSpace A 5 :=
  (zeroSpace A 5).add_mem (mDef_mem A 4) ((zeroSpace A 5).smul_mem _
    (zeroSpace_mono A (by decide : 3≤5) (h_in_grade_three A)))

def Sources (a d z x G H : K) : Prop :=
  (x=0 ∧ G=0 ∧ H=0) ∨ (x=a ∧ G=baseAmp a ∧ H=0) ∨
  (x=d ∧ G=0 ∧ H=hzero d d) ∨ (x=2*d ∧ G=0) ∨
  (x=z ∧ G=0 ∧ H=hzero d z)

theorem order9_native_sources (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 9)
    (oneOff : (supportedNodes A (g A)).card=1)
    {a d : K} {i j : Fin 12} (D : GlobalNormal A a d i j) (F : FirstFour A a d (by decide)) :
    ∀ l : Fin 12, l.val<6 →
      Sources a d (nodes A (5:Fin 12)) (nodes A l) (g A l) (scaledH A a l) := by
  intro l lr
  let z : K := nodes A (5:Fin 12)
  have an := D.base.origin.a_ne
  have dn := D.base.dn
  have cases : l=0 ∨ l=1 ∨ l=2 ∨ l=3 ∨ l=4 ∨ l=5 := by
    rcases show l.val=0 ∨ l.val=1 ∨ l.val=2 ∨ l.val=3 ∨ l.val=4 ∨ l.val=5 by omega with
      eq|eq|eq|eq|eq|eq
    · exact Or.inl (Fin.ext eq)
    · exact Or.inr (Or.inl (Fin.ext eq))
    · exact Or.inr (Or.inr (Or.inl (Fin.ext eq)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext eq))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext eq)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Fin.ext eq)))))
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl
  · have f : nodes A (0:Fin 12)=0 ∧ g A (0:Fin 12)=0 ∧ h A (0:Fin 12)=0 := by
      simpa [chartNode,chartDefect,chartH] using F.features 0
    exact Or.inl ⟨f.1,f.2.1,by rw [scaledH_eval,f.2.2,zero_div]⟩
  · have f : nodes A (1:Fin 12)=a ∧ g A (1:Fin 12)=baseAmp a ∧ h A (1:Fin 12)=0 := by
      simpa [chartNode,chartDefect,chartH] using F.features 1
    exact Or.inr (Or.inl ⟨f.1,f.2.1,by rw [scaledH_eval,f.2.2,zero_div]⟩)
  · have f : nodes A (2:Fin 12)=d ∧ g A (2:Fin 12)=0 ∧ h A (2:Fin 12)=twoHd a d := by
      simpa [chartNode,chartDefect,chartH] using F.features 2
    refine Or.inr (Or.inr (Or.inl ⟨f.1,f.2.1,?_⟩))
    rw [scaledH_eval,f.2.2,hzero,twoHd]
    field_simp [an,dn]
    ring
  · have f : nodes A (3:Fin 12)=2*d ∧ g A (3:Fin 12)=0 := by
      have e := F.features (3:Fin 4)
      simpa [chartNode,chartDefect] using And.intro e.1 e.2.1
    exact Or.inr (Or.inr (Or.inr (Or.inl f)))
  · have f := order9_fifth_feature ha ho oneOff D F
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨f.1,f.2.1⟩)))
  · have f := order9_sixth_feature ha ho oneOff D F
    change g A (5:Fin 12)=0 ∧ z≠0 ∧ z≠d ∧ z≠2*d ∧ h A (5:Fin 12)=_ ∧ _ at f
    refine Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl,f.1,?_⟩)))
    rw [scaledH_eval,f.2.2.2.2.1,hzero]
    field_simp [an,dn]

/-- Remove the single off-source contribution using the actual vector
Ag, before substituting the normalized physical moments. -/
theorem paid_on_actions {a d : K} {i j r : Fin 12} (D : GlobalNormal A a d i j)
    (gr : g A r=0) :
    let x := nodes A r
    let H := scaledH A a r
    M1 A r-(a/baseAmp a)*h A r=m1 x H ∧
    M2 A r-(a^2/baseAmp a)*h A r=m2 d x H ∧
    M3 A r-(a^3/baseAmp a)*h A r=m3 d x H := by
  let x := nodes A r
  have an := D.base.origin.a_ne
  have e3 : M3 A r=x^4/4+((2*d^2-2*a^2)/a)*h A r-(d/a)*x*h A r := by
    have e := congrFun D.q3 r
    simp only [mDef_apply,Nat.reduceAdd,Nat.cast_ofNat,Pi.add_apply,Pi.smul_apply,Pi.sub_apply,
      smul_eq_mul,diag_apply,gr,mul_zero,zero_add] at e
    linear_combination e
  change _=m1 x (scaledH A a r) ∧ _=m2 d x (scaledH A a r) ∧ _=m3 d x (scaledH A a r)
  rw [m1_relation,m2_relation D.base.q2,e3,scaledH_eval,gr]
  unfold m1 m2 m3 twoLam baseAmp x
  constructor
  · field_simp [an]
    ring
  constructor
  · field_simp [an]
    ring
  · field_simp [an]
    ring

def jSource (d z x : K) : K :=
  ((z-d)*x^3-d*(3*z-2*d)*x^2+2*d^2*z*x)/(4*d)

def vSource (d z x : K) : K :=
  (3*d+z)*x^3-(2*d^2+3*d*z)*x^2+2*d^2*z*x

/-- The two source identities are checked directly on all five feature
types, including both arbitrary H values on the same t=2d fibre. -/
theorem source_interpolation {a d z x G H : K} (an : a≠0) (dn : d≠0)
    (row : Sources a d z x G H) :
    x*H=2*d*H+jSource d z x-(jSource d z a/baseAmp a)*G ∧
    x^4=vSource d z x+((a^4-vSource d z a)/baseAmp a)*G := by
  rcases row with ⟨cc,gg,hh⟩|⟨cc,gg,hh⟩|⟨cc,gg,hh⟩|⟨cc,gg⟩|⟨cc,gg,hh⟩
  all_goals simp only [cc,gg,jSource,vSource,baseAmp,mul_zero,zero_mul]
  all_goals try rw [hh]
  all_goals constructor
  all_goals try simp only [hzero]
  all_goals (try field_simp [an,dn]) <;> (first | (simp [an,dn]; done) | ring)

theorem order9_actions_seven (ha : StrictLower A) {a d z : K} {i j r : Fin 12}
    (D : GlobalNormal A a d i j) (gr : g A r=0)
    (pre : ∀ l, l < r → Sources a d z (nodes A l) (g A l) (scaledH A a l)) :
    Jtest A a r=jValue d z (nodes A r) (scaledH A a r) ∧
    Vtest A a r=vValue d z (nodes A r) (scaledH A a r) := by
  let c := nodes A
  let H := scaledH A a
  let Jsrc := (z-d) • c^3-(d*(3*z-2*d)) • c^2+(2*d^2*z) • c
  let Vsrc := (3*d+z) • c^3-(2*d^2+3*d*z) • c^2+(2*d^2*z) • c
  let ja := jSource d z a/baseAmp a
  let va := (a^4-vSource d z a)/baseAmp a
  have an := D.base.origin.a_ne
  have dn := D.base.dn
  have hj := causal_action_eq ha r (diag c H) ((2*d) • H+(1/(4*d)) • Jsrc-ja • g A)
    (fun l lr=>by
      have e := (source_interpolation an dn (pre l lr)).1
      simp only [diag_apply,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,Pi.pow_apply,smul_eq_mul]
      dsimp only [Jsrc,c,H,ja] at *
      simp only [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,Pi.pow_apply,smul_eq_mul]
      unfold jSource at e ⊢
      linear_combination e)
  have hv := causal_action_eq ha r (c^4) (Vsrc+va • g A)
    (fun l lr=>by
      have e := (source_interpolation an dn (pre l lr)).2
      simp only [Vsrc,c,H,va,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,Pi.pow_apply,smul_eq_mul]
      unfold vSource at e ⊢
      linear_combination e)
  have hk : mat A H r=(d-c r)*H r := by
    have kh := congrFun D.hk r
    simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,diag_apply] at kh
    change (mat A (a⁻¹ • h A)) r=_
    rw [map_smul,Pi.smul_apply,smul_eq_mul]
    change a⁻¹*k A r=(d-c r)*H r
    rw [kh]
    simp only [H,c,scaledH,Pi.smul_apply,smul_eq_mul]
    ring
  obtain ⟨p1,p2,p3⟩ := paid_on_actions D gr
  have eV : Vtest A a r=mat A (c^4) r-(c r)^5/5+(2*a^2)*h A r := by
    simp only [Vtest,mDef_apply,Nat.reduceAdd,Nat.cast_ofNat,Pi.add_apply,Pi.smul_apply,smul_eq_mul,c]
  simp only [Jsrc,Vsrc,map_add,map_sub,map_smul,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul] at hj hv
  change Jtest A a r=(2*d)*mat A H r+1/(4*d)*((z-d)*M3 A r-
    (d*(3*z-2*d))*M2 A r+(2*d^2*z)*M1 A r)-ja*h A r at hj
  change mat A (c^4) r=(3*d+z)*M3 A r-(2*d^2+3*d*z)*M2 A r+
    (2*d^2*z)*M1 A r+va*h A r at hv
  constructor
  · rw [hj,hk]
    unfold jValue
    dsimp only [c,H]
    rw [←p1,←p2,←p3]
    dsimp only [ja,jSource]
    ring
  · rw [eV,hv]
    unfold vValue
    dsimp only [c,H]
    rw [←p1,←p2,←p3]
    dsimp only [va,vSource,baseAmp]
    field_simp [an]
    ring

end RKCert.Paired.OneOff.Seven
