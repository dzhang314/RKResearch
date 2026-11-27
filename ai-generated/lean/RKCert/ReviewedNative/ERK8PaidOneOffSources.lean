module
public import RKCert.ReviewedNative.ERK8PaidArithmetic

public import RKCert.ReviewedNative.ERK8PaidOneOffIndependentSquare

@[expose] public section

/-! # Causal moment relations for two charged source abscissas -/
namespace RKResearch.Certified.Graded.OneOff.PaidProof
open Module
open scoped Classical Matrix

variable {K : Type*} [Field K] [EightUnits K] {s : ℕ}
variable {A : Matrix (Fin s) (Fin s) K}

abbrev baseAmp (a : K) := -a^2/2
noncomputable abbrev M1 (A : Matrix (Fin s) (Fin s) K) := mat A (nodes A)
noncomputable abbrev M2 (A : Matrix (Fin s) (Fin s) K) := mat A ((nodes A)^2)
noncomputable abbrev M3 (A : Matrix (Fin s) (Fin s) K) := mat A ((nodes A)^3)

theorem m1_relation (A : Matrix (Fin s) (Fin s) K) (i : Fin s) :
    M1 A i=(nodes A i)^2/2+g A i := by
  rw [g_apply,add_comm,sub_add_cancel]

theorem m2_relation {a lam : K} (Q : mDef A 2=(2*a/3) • g A+lam • h A)
    (i : Fin s) : M2 A i=(nodes A i)^3/3+(2*a/3)*g A i+lam*h A i := by
  have e := congrFun Q i
  simp only [mDef_apply2,mDef_apply3,mDef_apply4,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Nat.reduceAdd,Nat.cast_ofNat] at e
  linear_combination (norm := eight_ring K) e

theorem m3_relation {a mu nu : K} {Z : Fin s → K}
    (Q : mDef A 3=((a^2/2) • g A+mu • h A)+nu • Z) (i : Fin s) :
    M3 A i=(nodes A i)^4/4+(a^2/2)*g A i+mu*h A i+nu*Z i := by
  have e := congrFun Q i
  simp only [mDef_apply2,mDef_apply3,mDef_apply4,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Nat.reduceAdd,Nat.cast_ofNat] at e
  linear_combination (norm := eight_ring K) e

omit [EightUnits K] in
theorem exists_first_nonzero {v : Fin s → K} (vn : v≠0) :
    ∃ i, v i≠0 ∧ ∀ j, j < i → v j=0 := by
  let S : Set (Fin s) := {i | v i≠0}
  have ex : S.Nonempty := by
    by_contra e
    apply vn
    ext i
    change v i=0
    by_contra h
    exact e ⟨i,h⟩
  obtain ⟨i,hi,hmin⟩ := wellFounded_lt.has_min S ex
  refine ⟨i,hi,fun j hj => ?_⟩
  by_contra h
  exact hmin j h hj

omit [EightUnits K] in
theorem three_sources_cubic (ha : ∀ i j, i ≤ j → A i j = 0) (a d : K) (i : Fin s)
    (pre : ∀ j, j < i → nodes A j=0 ∨ nodes A j=a ∨ nodes A j=d) :
    M3 A i=(a+d)*M2 A i-a*d*M1 A i := by
  have e := causal_action_eq ha i ((nodes A)^3)
    ((a+d) • (nodes A)^2-(a*d) • nodes A) (fun j hj => by
      rcases pre j hj with x|x|x <;>
        simp only [Pi.pow_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,x] <;> eight_ring K)
  simpa only [map_sub,map_smul,Pi.sub_apply,Pi.smul_apply,smul_eq_mul] using e

theorem c4_one_clock_next (ha : ∀ i j, i ≤ j → A i j = 0) (a : K) (i : Fin s)
    (pre : ∀ j, j < i → nodes A j=0 ∨ nodes A j=a)
    (d1 : g A i=0) (d2 : mDef A 2 i=0) (d3 : mDef A 3 i=0) :
    nodes A i=0 := by
  have e1 := m1_relation A i
  rw [d1,add_zero] at e1
  simp only [mDef_apply2,mDef_apply3,mDef_apply4,clock_power_action ha 1 pre,clock_power_action ha 2 pre,
    e1,pow_one,Nat.reduceAdd,Nat.cast_ofNat] at d2 d3
  by_contra x0
  have e2 : nodes A i=3*a/2 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 x0)
    linear_combination (norm := eight_ring K) -3*d2
  have e3 : (nodes A i)^2=2*a^2 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 x0)
    linear_combination (norm := eight_ring K) -4*d3
  rw [e2] at e3
  have a0 : a=0 := by
    by_contra an
    exact pow_ne_zero 2 an (show a^2=0 by linear_combination (norm := eight_ring K) 4*e3)
  exact x0 (by rw [e2,a0]; simp)

/-- A first nonzero clock outside two old source clocks, if C(4) holds
there, must hit the explicit quadratic. -/
theorem c4_two_clock_next (ha : ∀ i j, i ≤ j → A i j = 0) (a d : K) (i : Fin s)
    (pre : ∀ j, j < i → nodes A j=0 ∨ nodes A j=a ∨ nodes A j=d)
    (d1 : g A i=0) (d2 : mDef A 2 i=0) (d3 : mDef A 3 i=0)
    (x0 : nodes A i≠0) : 3*(nodes A i)^2-4*(a+d)*nodes A i+6*a*d=0 := by
  have e1 := m1_relation A i
  rw [d1,add_zero] at e1
  simp only [mDef_apply2,mDef_apply3,mDef_apply4,Nat.reduceAdd,Nat.cast_ofNat] at d2 d3
  have e := three_sources_cubic ha a d i pre
  apply (mul_eq_zero.mp (show (nodes A i)^2*(3*(nodes A i)^2-4*(a+d)*nodes A i+6*a*d)=0 by
    linear_combination (norm := eight_ring K) 12*e-12*d3+12*(a+d)*d2-12*a*d*e1)).resolve_left
  exact pow_ne_zero 2 x0

theorem c4_support_one_impossible (ha : ∀ i j, i ≤ j → A i j = 0)
    (sep : PolySeparated A 4) (a : K)
    (hC : ∀ i, nodes A i≠a → g A i=0 ∧ mDef A 2 i=0 ∧ mDef A 3 i=0) : False := by
  apply sep.knots_not_cover ({0,a}:Finset K) ((Finset.card_insert_le ..).trans (by simp))
  let S : Set (Fin s) := {i | nodes A i≠0 ∧ nodes A i≠a}
  have none : ¬S.Nonempty := by
    intro ex
    obtain ⟨i,hi,hmin⟩ := wellFounded_lt.has_min S ex
    obtain ⟨xn,xa⟩ := show nodes A i≠0 ∧ nodes A i≠a from hi
    obtain ⟨g0,m2,m3⟩ := hC i xa
    have pre (j : Fin s) (hj : j < i) : nodes A j=0 ∨ nodes A j=a := by
      by_contra! outside
      exact hmin j outside hj
    exact xn (c4_one_clock_next ha a i pre g0 m2 m3)
  intro i
  by_contra e
  have h : nodes A i≠0 ∧ nodes A i≠a := by simpa using e
  exact none ⟨i,h⟩

theorem c4_support_two_impossible (ha : ∀ i j, i ≤ j → A i j = 0)
    (sep : PolySeparated A 4) (a d r : K) (rOld : r=a ∨ r=d)
    (squared : ∀ x : K, 3*x^2-4*(a+d)*x+6*a*d=3*(x-r)^2)
    (hC : ∀ i, nodes A i≠a → nodes A i≠d →
      g A i=0 ∧ mDef A 2 i=0 ∧ mDef A 3 i=0) : False := by
  apply sep.knots_not_cover ({0,a,d}:Finset K)
    ((Finset.card_insert_le ..).trans (Nat.succ_le_succ ((Finset.card_insert_le ..).trans (by simp))))
  let S : Set (Fin s) := {i | nodes A i≠0 ∧ nodes A i≠a ∧ nodes A i≠d}
  have none : ¬S.Nonempty := by
    intro ex
    obtain ⟨i,hi,hmin⟩ := wellFounded_lt.has_min S ex
    obtain ⟨xn,xa,xd⟩ := show nodes A i≠0 ∧ nodes A i≠a ∧ nodes A i≠d from hi
    obtain ⟨g0,m2,m3⟩ := hC i xa xd
    have pre (j : Fin s) (hj : j < i) : nodes A j=0 ∨ nodes A j=a ∨ nodes A j=d := by
      by_contra! outside
      exact hmin j outside hj
    have h := c4_two_clock_next ha a d i pre g0 m2 m3 xn
    rw [squared] at h
    have ea : nodes A i=r := by
      by_contra e
      exact mul_ne_zero (by eight_num) (pow_ne_zero 2 (sub_ne_zero.mpr e)) h
    exact rOld.elim (fun e=>xa (ea.trans e)) (fun e=>xd (ea.trans e))
  intro i
  by_contra e
  have h : nodes A i≠0 ∧ nodes A i≠a ∧ nodes A i≠d := by simpa using e
  exact none ⟨i,h⟩

/-- Three preceding features in the on-first chart. -/
def ThreeFeatures (a d hd x G H : K) : Prop :=
  (x=0 ∧ G=0 ∧ H=0) ∨ (x=a ∧ G=baseAmp a ∧ H=0) ∨ (x=d ∧ G=0 ∧ H=hd)

/-- A later prefix can add one changed-amplitude row at the same off clock. -/
def FourFeatures (a d hd v gam x G H : K) : Prop :=
  ThreeFeatures a d hd x G H ∨ (x=a ∧ G=v ∧ H=gam*(v-baseAmp a))

omit [EightUnits K] in
theorem four_features_clocks {a d hd v gam x G H : K}
    (F : FourFeatures a d hd v gam x G H) : x=0 ∨ x=a ∨ x=d := by
  rcases F with (e|e|e)|e
  · exact Or.inl e.1
  · exact Or.inr (Or.inl e.1)
  · exact Or.inr (Or.inr e.1)
  · exact Or.inr (Or.inl e.1)

theorem three_sources_actions (ha : ∀ i j, i ≤ j → A i j = 0) {a d hd : K} (i : Fin s)
    (an : a≠0) (hn : hd≠0)
    (pre : ∀ j, j < i → ThreeFeatures a d hd (nodes A j) (g A j) (h A j)) :
    M1 A i=(a/baseAmp a)*h A i+(d/hd)*k A i ∧
    M2 A i=(a^2/baseAmp a)*h A i+(d^2/hd)*k A i ∧
    M3 A i=(a^3/baseAmp a)*h A i+(d^3/hd)*k A i := by
  have un : baseAmp a≠0 := div_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ an)) (by eight_num)
  have actions (n : ℕ) (nn : n≠0) :
      mat A ((nodes A)^n) i=(a^n/baseAmp a)*h A i+(d^n/hd)*k A i := by
    have source (j : Fin s) (hj : j < i) :
        ((nodes A)^n) j=((a^n/baseAmp a) • g A+(d^n/hd) • h A) j := by
      rcases pre j hj with ⟨x,G,H⟩|⟨x,G,H⟩|⟨x,G,H⟩ <;>
        simp [x,G,H,nn,un,hn]
    have e := causal_action_eq ha i _ _ source
    simpa only [map_add,map_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul,mat_g] using e
  exact ⟨by simpa only [pow_one] using actions 1 (by decide),
    actions 2 (by decide),actions 3 (by decide)⟩

/-- Exact source interpolation for the changed-amplitude features. This
does not identify or merge coordinates carrying the same feature. -/
theorem four_sources_h_action (ha : ∀ i j, i ≤ j → A i j = 0) {a d hd v gam : K} (i : Fin s)
    (_an : a≠0) (dn : d≠0) (ad : d≠a)
    (pre : ∀ j, j < i → FourFeatures a d hd v gam (nodes A j) (g A j) (h A j)) :
    k A i=(hd/d)*(M2 A i-a*M1 A i)/(d-a)+
      gam*(h A i-(baseAmp a/a)*(d*M1 A i-M2 A i)/(d-a)) := by
  have con (x G H : K) (F : FourFeatures a d hd v gam x G H) :
      H=(hd/d)*(x^2-a*x)/(d-a)+gam*(G-(baseAmp a/a)*(d*x-x^2)/(d-a)) := by
    rcases F with (⟨hx,hg,hh⟩|⟨hx,hg,hh⟩|⟨hx,hg,hh⟩)|⟨hx,hg,hh⟩ <;>
      rw [hx,hg,hh] <;> field_simp [two_paid K,three_paid K,four_paid K,five_paid K,six_paid K,seven_paid K,eight_paid K,nine_paid K,twelve_paid K,fourteen_paid K,thirtyTwo_paid K,_an,dn,sub_ne_zero.mpr ad] <;> eight_ring K
  let u := ((hd/d)/(d-a)) • ((nodes A)^2-a • nodes A) +
    gam • (g A-((baseAmp a/a)/(d-a)) • (d • nodes A-(nodes A)^2))
  have e := causal_action_eq ha i (h A) u (fun j hj => by
    have z := con _ _ _ (pre j hj)
    simp only [u,Pi.add_apply,Pi.sub_apply,Pi.pow_apply,Pi.smul_apply,smul_eq_mul]
    linear_combination (norm := eight_ring K) z)
  simp only [u,map_add,map_sub,map_smul,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,
    smul_eq_mul,mat_g] at e
  linear_combination (norm := eight_ring K) e

end RKResearch.Certified.Graded.OneOff.PaidProof
