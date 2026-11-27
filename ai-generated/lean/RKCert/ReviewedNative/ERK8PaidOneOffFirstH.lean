module
public import RKCert.ReviewedNative.ERK8PaidArithmetic
public import RKCert.ReviewedNative.ERK8PaidOneOffDebut

@[expose] public section

/-! # Actual first new forward feature at order nine

The two branches and calibration below are on the original physical
rows. In particular the leading submatrix in the restriction theorem
is the reviewed tableau's literal prefix, not a quotient of states. -/
namespace RKResearch.Certified.Graded.OneOff.PaidProof
open RKResearch Module
open scoped Classical Matrix

variable {K : Type*} [Field K] [EightUnits K] {s p : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}

/-- Before the initial nonzero (Ag), every physical predecessor is on
at zero or has the first off feature. Features are not identified as rows. -/
def EarlyPrefix (A : Matrix (Fin s) (Fin s) K) (a : K) (j : Fin s) : Prop :=
  ∀ i, i < j →
    (nodes A i=0 ∧ g A i=0) ∨ (nodes A i=a ∧ g A i= -a^2/2)

private theorem early_aggregates {a : K} {j : Fin s}
    (ha : ∀ i j, i ≤ j → A i j = 0) (pre : EarlyPrefix A a j) :
    h A j=(-a/2)*mat A (nodes A) j ∧
    mat A ((nodes A)^2) j=a*mat A (nodes A) j := by
  have hg (i : Fin s) (hi : i < j) :
      (g A-(-a/2:K) • nodes A) i=0 := by
    rcases pre i hi with ⟨hn,hd⟩|⟨hn,hd⟩
    · simp [hn,hd]
    · simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,hn,hd]
      eight_ring K
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
    (ha : ∀ i j, i ≤ j → A i j = 0) (O : Origin A a i) (vanish : ∀ k, k < j → h A k=0) :
    EarlyPrefix A a j := by
  intro k
  refine wellFounded_lt.induction (C:=fun k : Fin s => k < j →
    (nodes A k=0 ∧ g A k=0) ∨ (nodes A k=a ∧ g A k= -a^2/2)) k ?_
  intro k ih hk
  have pre : EarlyPrefix A a k := fun l hl => ih l hl (hl.trans hk)
  have hp := (early_aggregates ha pre).1
  have hn : (-a/2 : K) ≠ 0 := div_ne_zero (neg_ne_zero.mpr O.a_ne) (by eight_num)
  have hh : mat A (nodes A) k=0 := (mul_eq_zero.mp (hp.symm.trans (vanish k hk))).resolve_left hn
  have gg : g A k= -(nodes A k)^2/2 := by rw [g_apply,hh]; eight_ring K
  by_cases c0 : nodes A k=0
  · exact Or.inl ⟨c0,by simp [gg,c0]⟩
  · have gn : g A k≠0 := by
      rw [gg]
      exact div_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ c0)) (by eight_num)
    have ca := O.off_support k gn
    exact Or.inr ⟨ca,by rw [gg,ca]⟩

/-- The first (Ag) innovation is either on at a nonzero clock, or has
a genuinely different off defect amplitude. -/
structure FirstH (A : Matrix (Fin s) (Fin s) K) (a lam : K) (j : Fin s) : Prop where
  nonzero : h A j≠0
  earlier : ∀ i, i < j → h A i=0
  prefix_features : EarlyPrefix A a j
  alternative :
    (g A j=0 ∧ nodes A j≠0 ∧
      h A j= -a*(nodes A j)^2/4 ∧ lam=4*nodes A j/(3*a)-2) ∨
    (g A j≠0 ∧ g A j≠ -a^2/2 ∧ nodes A j=a ∧
      h A j= -a*(g A j+a^2/2)/2 ∧ lam= -2/3)

theorem first_h_split {a lam : K} {i : Fin s}
    (ha : ∀ i j, i ≤ j → A i j = 0) (hsep : ∀ a, coeffEval A 3 a ∈ zeroSpace A 3 → a = 0) (O : Origin A a i)
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
    linear_combination (norm := eight_ring K) -ez
  rw [ca] at hJ cJ
  have eq := congrFun qform j
  rw [mDef_apply2,cJ] at eq
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Nat.reduceAdd,Nat.cast_ofNat] at eq
  refine ⟨j,⟨hj,pre,pre',?_⟩⟩
  by_cases gj : g A j=0
  · left
    rw [gj,add_zero] at hJ
    have hd : nodes A j≠0 := fun e => hj (by rw [hJ,e]; simp)
    refine ⟨gj,hd,?_,?_⟩
    · linear_combination (norm := eight_ring K) hJ
    · apply mul_right_cancel₀ hj
      rw [gj,add_zero, mul_zero,zero_add] at eq
      calc
        lam*h A j = a*((nodes A j)^2/2)-(nodes A j)^3/3 := eq.symm
        _ = (4*nodes A j/(3*a)-2)*h A j := by
          rw [hJ]
          field_simp [two_paid K,three_paid K,four_paid K,five_paid K,six_paid K,seven_paid K,eight_paid K,nine_paid K,twelve_paid K,fourteen_paid K,thirtyTwo_paid K,O.a_ne]
          eight_ring K
  · right
    have cj := O.off_support j gj
    rw [cj] at hJ eq
    have gn : g A j≠ -a^2/2 := by
      intro e
      apply hj
      rw [hJ,e]
      eight_ring K
    refine ⟨gj,gn,cj,?_,?_⟩
    · linear_combination (norm := eight_ring K) hJ
    · apply mul_right_cancel₀ hj
      linear_combination (norm := eight_ring K) -eq + (2/3:K)*hJ


/-- The first innovation's physical predecessor tableau contains only the
initial two features and has no nonzero integrated quadratic residual. -/
theorem FirstH.restricted_profile {a lam : K} {j : Fin s}
    (F : FirstH A a lam j) (ha : ∀ i j, i ≤ j → A i j = 0) :
    h (prefixMatrix A j.isLt.le) = 0 ∧
    ∀ i : Fin j.val,
      (nodes (prefixMatrix A j.isLt.le) i = 0 ∧ g (prefixMatrix A j.isLt.le) i = 0) ∨
      (nodes (prefixMatrix A j.isLt.le) i = a ∧ g (prefixMatrix A j.isLt.le) i = -a^2/2) := by
  constructor
  · rw [h_prefix ha]
    ext i
    exact F.earlier (Fin.castLE j.isLt.le i) i.isLt
  · intro i
    simp only [nodes_prefix ha, prefixRestrict_apply, g, mDef_prefix ha j.isLt.le 1 (by decide)]
    exact F.prefix_features (Fin.castLE j.isLt.le i) i.isLt

/-- Forward half of the low-order saturation chart. The sole imported
budget is an upper rank of eight at grade four; row and tree identities
remain on the reviewed order condition. -/
theorem forward_minimal_ranks {n : ℕ} {A : Matrix (Fin (n+1)) (Fin (n+1)) K}
    {b : Fin (n+1) → K} (ha : ∀ i j, i ≤ j → A i j = 0)
    (ho : HasOrder p A b) (hp : 8 ≤ p) (cap : finrank K (treeSpace A 4) ≤ 8) :
    finrank K (zeroSpace A 3) = 2 ∧ finrank K (zeroSpace A 4) = 3 ∧
    finrank K (treeSpace A 3) = 6 ∧ finrank K (treeSpace A 4) = 8 := by
  have h4 := explicit_midpoint_rank_eq ha ho (q:=4) (by omega) (by omega)
  have h3 := explicit_midpoint_rank_eq ha ho (q:=3) (by omega) (by omega)
  have hf3 := zeroSpace_finrank ha ho (n:=2) (by omega)
  change 2 ≤ finrank K (zeroSpace A 3) at hf3
  have hlt := Submodule.finrank_lt_finrank_of_lt
    (zeroSpace_strict_paid8 ha (explicit_coeff_separated ha ho (q:=4) (by omega))
      (j:=3) (by decide) (by decide))
  change finrank K (zeroSpace A 3) < finrank K (zeroSpace A 4) at hlt
  omega

/-- The actual chronology from the order witnesses and the rank-two
hypothesis. No separate coefficients, nodes, or putative states are supplied. -/
theorem first_h_of_actual {n : ℕ} {A : Matrix (Fin (n+1)) (Fin (n+1)) K}
    {b : Fin (n+1) → K} (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder p A b)
    (hN : (offKnots A).card = 1) (hp : 6 ≤ p)
    (rank : finrank K (zeroSpace A 3) = 2) :
    ∃ (a : K) (i : Fin (n+1)) (lam : K) (j : Fin (n+1)), Origin A a i ∧
      zeroSpace A 3 = Submodule.span K {g A, h A} ∧
      mDef A 2 = (2*a/3) • g A + lam • h A ∧ FirstH A a lam j := by
  have sep := explicit_coeff_separated ha ho (q:=3) hp
  have hc : ∃ i, nodes A i ≠ 0 := by
    by_contra! z
    have eq : nodes A = 0 := funext z
    exact nodes_not_defect_of_separation (by decide) sep (eq ▸ (zeroSpace A 3).zero_mem)
  obtain ⟨a,i,O⟩ := origin_of_single_off ha hN hc
  obtain ⟨lam,qform⟩ := quadratic_defect_form ha sep rank O
  obtain ⟨j,F⟩ := first_h_split ha sep O qform
  exact ⟨a,i,lam,j,O,rank_two_span ha sep rank O,qform,F⟩

end RKResearch.Certified.Graded.OneOff.PaidProof
