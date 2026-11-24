module

public import RKCert.ERKOrderNineOneOffSeed
public import RKCert.ERKLowLobatto

@[expose] public section

namespace RKCert.Paired.OneOff
open Module Polynomial RKCert.Endpoint
open scoped Classical

variable {K : Type*} [Field K] [CharZero K] {s p : ℕ}
variable {A : Fin s → Fin s → K} {b : Vec K s}

/-- Before the initial nonzero (Ag), every physical predecessor is on
at zero or has the first off feature. Features are not identified as rows. -/
def EarlyPrefix (A : Fin s → Fin s → K) (a : K) (j : Fin s) : Prop :=
  ∀ i, i < j →
    (nodes A i=0 ∧ g A i=0) ∨ (nodes A i=a ∧ g A i= -a^2/2)

private theorem early_aggregates {a : K} {j : Fin s}
    (ha : StrictLower A) (pre : EarlyPrefix A a j) :
    h A j=(-a/2)*mat A (nodes A) j ∧
    mat A ((nodes A)^2) j=a*mat A (nodes A) j := by
  have hg (i : Fin s) (hi : i < j) :
      (g A-(-a/2:K) • nodes A) i=0 := by
    rcases pre i hi with ⟨hn,hd⟩|⟨hn,hd⟩
    · simp [hn,hd]
    · simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,hn,hd]
      ring
  have hc (i : Fin s) (hi : i < j) :
      ((nodes A)^2-a • nodes A) i=0 := by
    rcases pre i hi with ⟨hn,_⟩|⟨hn,_⟩
    · simp [hn]
    · simp [hn,pow_two]
  have eg := causal_mat ha j _ hg
  have ec := causal_mat ha j _ hc
  simp only [map_sub,map_smul,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,sub_eq_zero] at eg ec
  exact ⟨eg,ec⟩

theorem early_prefix_of_h_zero {a : K} {i j : Fin s}
    (ha : StrictLower A) (O : Origin A a i) (vanish : ∀ k, k < j → h A k=0) :
    EarlyPrefix A a j := by
  intro k
  refine wellFounded_lt.induction (C:=fun k : Fin s => k < j →
    (nodes A k=0 ∧ g A k=0) ∨ (nodes A k=a ∧ g A k= -a^2/2)) k ?_
  intro k ih hk
  have pre : EarlyPrefix A a k := fun l hl => ih l hl (hl.trans hk)
  have hp := (early_aggregates ha pre).1
  have hn : (-a/2 : K) ≠ 0 := div_ne_zero (neg_ne_zero.mpr O.a_ne) (by norm_num)
  have hh : mat A (nodes A) k=0 := (mul_eq_zero.mp (hp.symm.trans (vanish k hk))).resolve_left hn
  have gg : g A k= -(nodes A k)^2/2 := by rw [g_apply,hh]; ring
  by_cases c0 : nodes A k=0
  · exact Or.inl ⟨c0,by simp [gg,c0]⟩
  · have gn : g A k≠0 := by
      rw [gg]
      exact div_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ c0)) (by norm_num)
    have ca := O.off_support k gn
    exact Or.inr ⟨ca,by rw [gg,ca]⟩

/-- The first (Ag) innovation is either on at a nonzero clock, or has
a genuinely different off defect amplitude. -/
structure FirstH (A : Fin s → Fin s → K) (a lam : K) (j : Fin s) : Prop where
  nonzero : h A j≠0
  earlier : ∀ i, i < j → h A i=0
  prefix_features : EarlyPrefix A a j
  alternative :
    (g A j=0 ∧ nodes A j≠0 ∧
      h A j= -a*(nodes A j)^2/4 ∧ lam=4*nodes A j/(3*a)-2) ∨
    (g A j≠0 ∧ g A j≠ -a^2/2 ∧ nodes A j=a ∧
      h A j= -a*(g A j+a^2/2)/2 ∧ lam= -2/3)

theorem first_h_split {a lam : K} {i : Fin s}
    (ha : StrictLower A) (hsep : Separated A 3) (O : Origin A a i)
    (qform : mDef A 2=(2*a/3) • g A+lam • h A) :
    ∃ j, FirstH A a lam j := by
  have hne : h A≠0 := fun e => h_not_in_g_span ha hsep O (e ▸ (Submodule.span K {g A}).zero_mem)
  let S : Set (Fin s) := {j | h A j≠0}
  have hex : S.Nonempty := by
    by_contra abs
    apply hne
    ext j
    change h A j=0
    by_contra q
    exact abs ⟨j,q⟩
  obtain ⟨j,hj,hmin⟩ := wellFounded_lt.has_min S hex
  change h A j≠0 at hj
  have pre (k : Fin s) (hk : k < j) : h A k=0 := by
    by_contra n
    exact hmin k n hk
  have pre' := early_prefix_of_h_zero ha O pre
  have ⟨hJ,cJ⟩ := early_aggregates ha pre'
  have ca : mat A (nodes A) j= (nodes A j)^2/2+g A j := by
    have ez := g_apply A j
    linear_combination -ez
  rw [ca] at hJ cJ
  have eq := congrFun qform j
  rw [mDef_apply,cJ] at eq
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Nat.reduceAdd,Nat.cast_ofNat] at eq
  refine ⟨j,⟨hj,pre,pre',?_⟩⟩
  by_cases gj : g A j=0
  · left
    rw [gj,add_zero] at hJ
    have hd : nodes A j≠0 := fun e => hj (by rw [hJ,e]; simp)
    refine ⟨gj,hd,?_,?_⟩
    · linear_combination hJ
    · apply mul_right_cancel₀ hj
      rw [gj,add_zero, mul_zero,zero_add] at eq
      calc
        lam*h A j = a*((nodes A j)^2/2)-(nodes A j)^3/3 := eq.symm
        _ = (4*nodes A j/(3*a)-2)*h A j := by
          rw [hJ]
          field_simp [O.a_ne]
          ring
  · right
    have cj := O.off_support j gj
    rw [cj] at hJ eq
    have gn : g A j≠ -a^2/2 := by
      intro e
      apply hj
      rw [hJ,e]
      ring
    refine ⟨gj,gn,cj,?_,?_⟩
    · linear_combination hJ
    · apply mul_right_cancel₀ hj
      linear_combination -eq + (2/3:K)*hJ

omit [CharZero K] in
theorem clocks_not_covered_by_four (hsep : Separated A 4) (T : Finset K) (hT : T.card≤4) :
    ¬ ∀ i, nodes A i∈T := by
  intro all
  have hP : evalNodes A (nodalHull T)=0 := by
    ext i
    rw [evalNodes_apply,Pi.zero_apply,nodalHull_eval_of_mem (all i)]
  have hdeg : (nodalHull T).natDegree≤4 := natDegree_nodalHull T ▸ hT
  exact (monic_nodalHull T).ne_zero (hsep _ hdeg (hP ▸ (zeroSpace A 4).zero_mem))

theorem first_h_of_actual {q : ℕ} (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b q)
    (hN : (supportedNodes A (g A)).card=1) (hp : 6≤q) (hs : 0 < s)
    (rank : finrank K (zeroSpace A 3)=2) :
    ∃ (a : K) (i : Fin s) (lam : K) (j : Fin s), Origin A a i ∧
      zeroSpace A 3=twoSpan (g A) (h A) ∧
      mDef A 2=(2*a/3) • g A+lam • h A ∧ FirstH A a lam j := by
  have hsep : Separated A 3 := explicit_separated ha ho hp hs
  have hc : ∃ i, nodes A i≠0 := by
    by_contra! n
    have eq : nodes A=0 := funext n
    exact nodes_not_zeroSpace hsep (by decide) (eq ▸ (zeroSpace A 3).zero_mem)
  obtain ⟨a,i,O⟩ := origin_of_single_off ha hN hc
  obtain ⟨lam,qform⟩ := quadratic_defect_form ha ho (by omega) hsep rank O
  obtain ⟨j,F⟩ := first_h_split ha hsep O qform
  exact ⟨a,i,lam,j,O,rank_two_span ha ho (by omega) hsep rank O,qform,F⟩

/-- Actual p9 one-off input, before constant-amplitude and prefix closure. -/
theorem order9_first_h {A : Fin 12 → Fin 12 → K} {b : Vec K 12}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 9)
    (hN : (supportedNodes A (g A)).card=1) :
    ∃ (a : K) (i : Fin 12) (lam : K) (j : Fin 12), Origin A a i ∧
      zeroSpace A 3=twoSpan (g A) (h A) ∧
      mDef A 2=(2*a/3) • g A+lam • h A ∧ FirstH A a lam j := by
  have rr := (order9_twelve_stage_chart ha ho).2.1
  exact first_h_of_actual ha ho hN (by decide) (by decide) rr

/-- The same genuinely physical first-event chart already holds at p8. -/
theorem order8_first_h {A : Fin 10 → Fin 10 → K} {b : Vec K 10}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 8)
    (hN : (supportedNodes A (g A)).card=1) :
    ∃ (a : K) (i : Fin 10) (lam : K) (j : Fin 10), Origin A a i ∧
      zeroSpace A 3=twoSpan (g A) (h A) ∧
      mDef A 2=(2*a/3) • g A+lam • h A ∧ FirstH A a lam j := by
  obtain ⟨_,_,_,_,_,hr,_,_,_,_,_⟩ := order8_ten_stage_chart ha ho
  exact first_h_of_actual ha ho hN (by decide) (by decide) hr

end RKCert.Paired.OneOff
