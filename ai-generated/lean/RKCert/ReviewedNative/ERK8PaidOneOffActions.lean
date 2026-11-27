module
public import RKCert.ReviewedNative.ERK8PaidArithmetic

public import RKCert.ReviewedNative.ERK8PaidOneOffRows

@[expose] public section

/-! The published order-free five-type scalar identities are applied
causally to the **six actual predecessor rows** of the Fin 10 tableau.
No order-nine tableau or paid order-nine action is used. -/
namespace RKResearch.Certified.Graded.OneOff.PaidProof.Eight

open RKResearch Module Polynomial
open scoped Classical Matrix

variable {K : Type*} [Field K] [EightUnits K] {A : Matrix (Fin 10) (Fin 10) K} {b : Fin 10 → K}

def Sources (a d z x G H : K) : Prop :=
  (x=0 ∧ G=0 ∧ H=0) ∨ (x=a ∧ G=baseAmp a ∧ H=0) ∨
  (x=d ∧ G=0 ∧ H=hzero d d) ∨ (x=2*d ∧ G=0) ∨
  (x=z ∧ G=0 ∧ H=hzero d z)

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
  all_goals field_simp [two_paid K,three_paid K,four_paid K,five_paid K,six_paid K,seven_paid K,eight_paid K,nine_paid K,twelve_paid K,fourteen_paid K,thirtyTwo_paid K,an,dn]
  all_goals (first | (simp_all; done) | eight_ring K)

noncomputable def scaled (A : Matrix (Fin 10) (Fin 10) K) (a : K) : Fin 10 → K := a⁻¹ • h A

omit [EightUnits K] in
theorem scaled_eval (a : K) (r : Fin 10) :
    scaled A a r=h A r/a := by
  simp [scaled,div_eq_mul_inv,mul_comm]

noncomputable def jTest (A : Matrix (Fin 10) (Fin 10) K) (a : K) : Fin 10 → K :=
  mat A (diag (nodes A) (scaled A a))

noncomputable def vTest (A : Matrix (Fin 10) (Fin 10) K) (a : K) : Fin 10 → K :=
  mDef A 4+(2*a^2) • h A

theorem jTest_mem (ho : HasOrder 8 A b) (a : K) : jTest A a∈zeroSpace A 5 := by
  unfold jTest scaled
  rw [map_smul,map_smul]
  exact (zeroSpace A 5).smul_mem _ (mat_zeroSpace ho 4 (by decide)
    (diag_zeroSpace A 3 (h_in_grade_three A)))

theorem vTest_mem (A : Matrix (Fin 10) (Fin 10) K) (a : K) : vTest A a∈zeroSpace A 5 :=
  (zeroSpace A 5).add_mem (mDef_mem A 4) ((zeroSpace A 5).smul_mem _
    (zeroSpace_mono A (by decide : 3≤5) (h_in_grade_three A)))

theorem nativeSixSources
    {a d : K} {i j : Fin 10} (D : GlobalNormal A a d i j) (P : PhysicalPrefix A a d) :
    ∀ l : Fin 10, l.val<6 →
      Sources a d (nodes A (5:Fin 10)) (nodes A l) (g A l) (scaled A a l) := by
  intro l lr
  let F := P.first
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
  · have f : nodes A (0:Fin 10)=0 ∧ g A (0:Fin 10)=0 ∧ h A (0:Fin 10)=0 := by
      simpa [chartNode,chartDefect,chartH] using F.features 0
    exact Or.inl ⟨f.1,f.2.1,by rw [scaled_eval,f.2.2,zero_div]⟩
  · have f : nodes A (1:Fin 10)=a ∧ g A (1:Fin 10)=baseAmp a ∧ h A (1:Fin 10)=0 := by
      simpa [chartNode,chartDefect,chartH] using F.features 1
    exact Or.inr (Or.inl ⟨f.1,f.2.1,by rw [scaled_eval,f.2.2,zero_div]⟩)
  · have f : nodes A (2:Fin 10)=d ∧ g A (2:Fin 10)=0 ∧ h A (2:Fin 10)=twoHd a d := by
      simpa [chartNode,chartDefect,chartH] using F.features 2
    refine Or.inr (Or.inr (Or.inl ⟨f.1,f.2.1,?_⟩))
    rw [scaled_eval,f.2.2,hzero,twoHd]
    field_simp [two_paid K,three_paid K,four_paid K,five_paid K,six_paid K,seven_paid K,eight_paid K,nine_paid K,twelve_paid K,fourteen_paid K,thirtyTwo_paid K,an,dn]
    eight_ring K
  · have f : nodes A (3:Fin 10)=2*d ∧ g A (3:Fin 10)=0 := by
      have e := F.features (3:Fin 4)
      simpa [chartNode,chartDefect] using And.intro e.1 e.2.1
    exact Or.inr (Or.inr (Or.inr (Or.inl f)))
  · have f := P.fifth
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨f.1,f.2.1⟩)))
  · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl,P.sixth.clean,?_⟩)))
    rw [scaled_eval,P.sixth.rawH,hzero]
    field_simp [two_paid K,three_paid K,four_paid K,five_paid K,six_paid K,seven_paid K,eight_paid K,nine_paid K,twelve_paid K,fourteen_paid K,thirtyTwo_paid K,an,dn] <;> eight_ring K

/-- Remove the single off-source contribution using the actual vector
Ag, before substituting the normalized physical moments. -/
theorem paidCleanActions {a d : K} {i j r : Fin 10} (D : GlobalNormal A a d i j)
    (gr : g A r=0) :
    let x := nodes A r
    let H := scaled A a r
    M1 A r-(a/baseAmp a)*h A r=m1 x H ∧
    M2 A r-(a^2/baseAmp a)*h A r=m2 d x H ∧
    M3 A r-(a^3/baseAmp a)*h A r=m3 d x H := by
  let x := nodes A r
  have an := D.base.origin.a_ne
  have e3 : M3 A r=x^4/4+((2*d^2-2*a^2)/a)*h A r-(d/a)*x*h A r := by
    have e := congrFun D.q3 r
    simp only [mDef_apply2,mDef_apply3,mDef_apply4,Nat.reduceAdd,Nat.cast_ofNat,Pi.add_apply,Pi.smul_apply,Pi.sub_apply,
      smul_eq_mul,diag_apply,gr,mul_zero,zero_add] at e
    linear_combination (norm := eight_ring K) e
  change _=m1 x (scaled A a r) ∧ _=m2 d x (scaled A a r) ∧ _=m3 d x (scaled A a r)
  rw [m1_relation,m2_relation D.base.q2,e3,scaled_eval,gr]
  unfold m1 m2 m3 twoLam baseAmp x
  constructor
  · field_simp [two_paid K,three_paid K,four_paid K,five_paid K,six_paid K,seven_paid K,eight_paid K,nine_paid K,twelve_paid K,fourteen_paid K,thirtyTwo_paid K,an]
    eight_ring K
  constructor
  · field_simp [two_paid K,three_paid K,four_paid K,five_paid K,six_paid K,seven_paid K,eight_paid K,nine_paid K,twelve_paid K,fourteen_paid K,thirtyTwo_paid K,an]
    eight_ring K
  · field_simp [two_paid K,three_paid K,four_paid K,five_paid K,six_paid K,seven_paid K,eight_paid K,nine_paid K,twelve_paid K,fourteen_paid K,thirtyTwo_paid K,an]
    eight_ring K

theorem causalJVAux (ha : ∀ i j, i ≤ j → A i j = 0) {a d z : K} {i j r : Fin 10}
    (D : GlobalNormal A a d i j) (gr : g A r=0)
    (pre : ∀ l, l < r → Sources a d z (nodes A l) (g A l) (scaled A a l)) :
    jTest A a r=jValue d z (nodes A r) (scaled A a r) ∧
    vTest A a r=vValue d z (nodes A r) (scaled A a r) := by
  let c := nodes A
  let H := scaled A a
  let Jsrc := (z-d) • c^3-(d*(3*z-2*d)) • c^2+(2*d^2*z) • c
  let Vsrc := (3*d+z) • c^3-(2*d^2+3*d*z) • c^2+(2*d^2*z) • c
  let ja := jSource d z a/baseAmp a
  let va := (a^4-vSource d z a)/baseAmp a
  have an := D.base.origin.a_ne
  have dn := D.base.dn
  have hj := causal_action_eq ha r (diag c H) ((2*d) • H+(1/(4*d)) • Jsrc-ja • g A)
    (fun l lr=>by
      have e := (source_interpolation an dn (pre l lr)).1
      simp only [diag_apply,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
      dsimp only [Jsrc,c,H,ja] at *
      simp only [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,Pi.pow_apply,smul_eq_mul]
      unfold jSource at e ⊢
      linear_combination (norm := eight_ring K) e)
  have hv := causal_action_eq ha r (c^4) (Vsrc+va • g A)
    (fun l lr=>by
      have e := (source_interpolation an dn (pre l lr)).2
      simp only [Vsrc,c,va,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,Pi.pow_apply,smul_eq_mul]
      unfold vSource at e ⊢
      linear_combination (norm := eight_ring K) e)
  have hk : mat A H r=(d-c r)*H r := by
    have kh := congrFun D.hk r
    simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,diag_apply] at kh
    change (mat A (a⁻¹ • h A)) r=_
    rw [map_smul,Pi.smul_apply,smul_eq_mul]
    change a⁻¹*k A r=(d-c r)*H r
    rw [kh]
    simp only [H,c,scaled,Pi.smul_apply,smul_eq_mul]
    eight_ring K
  obtain ⟨p1,p2,p3⟩ := paidCleanActions D gr
  have eV : vTest A a r=mat A (c^4) r-(c r)^5/5+(2*a^2)*h A r := by
    simp only [vTest,mDef_apply4,Nat.reduceAdd,Nat.cast_ofNat,Pi.add_apply,Pi.smul_apply,smul_eq_mul,c]
  simp only [Jsrc,Vsrc,map_add,map_sub,map_smul,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,mat_g] at hj hv
  change jTest A a r=(2*d)*mat A H r+1/(4*d)*((z-d)*M3 A r-
    (d*(3*z-2*d))*M2 A r+(2*d^2*z)*M1 A r)-ja*h A r at hj
  change mat A (c^4) r=(3*d+z)*M3 A r-(2*d^2+3*d*z)*M2 A r+
    (2*d^2*z)*M1 A r+va*h A r at hv
  constructor
  · rw [hj,hk]
    unfold jValue
    dsimp only [c,H]
    rw [←p1,←p2,←p3]
    dsimp only [ja,jSource]
    eight_ring K
  · rw [eV,hv]
    unfold vValue
    dsimp only [c,H]
    rw [←p1,←p2,←p3]
    dsimp only [va,vSource,baseAmp]
    field_simp [two_paid K,three_paid K,four_paid K,five_paid K,six_paid K,seven_paid K,eight_paid K,nine_paid K,twelve_paid K,fourteen_paid K,thirtyTwo_paid K,an]
    eight_ring K

theorem causalJV (ha : ∀ i j, i≤j → A i j=0) {a d : K} {i j r : Fin 10}
    (D : GlobalNormal A a d i j) (P : PhysicalPrefix A a d) (hr : r.val≤6) (gr : g A r=0) :
    let z := nodes A (5:Fin 10)
    jTest A a r=jValue d z (nodes A r) (scaled A a r) ∧
      vTest A a r=vValue d z (nodes A r) (scaled A a r) :=
  causalJVAux ha D gr (fun l lr=>nativeSixSources D P l (show l.val<6 from lt_of_lt_of_le lr hr))

noncomputable def wTest (A : Matrix (Fin 10) (Fin 10) K) (a d : K) : Fin 10 → K :=
  vTest A a-(4*d/5) • jTest A a

theorem wTest_mem (ho : HasOrder 8 A b) (a d : K) : wTest A a d∈zeroSpace A 5 :=
  (zeroSpace A 5).sub_mem (vTest_mem A a) ((zeroSpace A 5).smul_mem _ (jTest_mem ho a))

theorem wActual (ha : ∀ i j, i≤j → A i j=0) {a d : K} {i j r : Fin 10}
    (D : GlobalNormal A a d i j) (P : PhysicalPrefix A a d) (hr : r.val≤6) (gr : g A r=0) :
    let z := nodes A (5:Fin 10)
    let x := nodes A r
    let H := scaled A a r
    wTest A a d r+(4*d/5)*(x^2-2*d^2)*H =
      (x-2*d)*(x-z)*(4*d*H-x^2*(x-2*d))/5 := by
  obtain ⟨jVal,vVal⟩ := causalJV ha D P hr gr
  simpa only [wTest,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,jVal,vVal] using
    masterCombination d (nodes A (5:Fin 10)) (nodes A r) (scaled A a r) D.base.dn

end RKResearch.Certified.Graded.OneOff.PaidProof.Eight
