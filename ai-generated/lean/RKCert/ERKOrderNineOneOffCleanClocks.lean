module

public import RKCert.ERKOrderNineOneOffGlobalNormal

@[expose] public section

/-! # The three genuine clean Ag clocks, before numbered placement -/
namespace RKCert.Paired.OneOff
open Module 
open scoped Classical

variable {K : Type*} [Field K] [CharZero K] {s p : ℕ} {A : Fin s→Fin s→K}

theorem global_k_neg_delta {a d : K} {i j : Fin s} (D : GlobalNormal A a d i j) :
    k A= -deltaH A d := by
  rw [D.hk,deltaH]
  abel

/-- The first nonzero changed-clock Ag occurs on (2d), with the
exact amplitude of the fourth feature, without assuming its row number. -/
theorem first_doubled_clean_clock (ha : StrictLower A) (sep : Separated A 4)
    (rank3 : finrank K (zeroSpace A 3)=2) (rank4 : finrank K (zeroSpace A 4)=3)
    {a d : K} {i j : Fin s} (D : GlobalNormal A a d i j) :
    ∃ r,
      g A r=0 ∧ nodes A r=2*d ∧ h A r=a*d^2 ∧
      (∀ l, l < r → ThreeFeatures a d (twoHd a d) (nodes A l) (g A l) (h A l)) := by
  have an := D.base.origin.a_ne
  have dn := D.base.dn
  have zOut := deltaH_small_rank_impossible ha sep rank3 rank4 D.base
  have zn : deltaH A d≠0 := fun e=>zOut (e ▸ (zeroSpace A 3).zero_mem)
  obtain ⟨r,hn,prev⟩ := exists_first_nonzero zn
  have kp (l : Fin s) (lr : l < r) : k A l=0 := by rw [global_k_neg_delta D,Pi.neg_apply,prev l lr,neg_zero]
  have pre := normal_three_features_before ha D.base r kp
  obtain ⟨m1,off,clean⟩ := normal_head_row ha D.base r pre
  let x := nodes A r
  rw [deltaH_apply] at hn
  have cd : x≠d := sub_ne_zero.mp (left_ne_zero_of_mul hn)
  have Hne := right_ne_zero_of_mul hn
  have go : g A r=0 := by by_contra no; exact Hne (off no)
  have sc := clean go
  rw [m1_relation,go,add_zero] at m1
  have ka : k A r=a*x^2*(d-x)/4 := by linear_combination (1/4:K)*m1-(1/8:K)*sc
  have e : k A r=(d-x)*h A r := by
    rw [global_k_neg_delta D,Pi.neg_apply,deltaH_apply]
    dsimp only [x]
    ring
  have h : h A r=a*x^2/4 := by
    apply mul_left_cancel₀ (sub_ne_zero.mpr (Ne.symm cd))
    linear_combination -e+ka
  have xs : x≠0 := by intro y; exact Hne (by simp [h,y])
  have xx : x=2*d := by
    apply mul_left_cancel₀ (mul_ne_zero an (pow_ne_zero 2 xs))
    linear_combination -(1/2:K)*(sc-4*d*h)
  refine ⟨r,go,xx,?_,pre⟩
  rw [h,xx]
  ring

/-- The exact initial feature polynomial. It is zero on every off row,
even when a clean copy has that same abscissa. -/
noncomputable def cleanClockTest (A : Fin s→Fin s→K) (a d : K) : Vec K s :=
  (nodes A)^3-(3*d) • (nodes A)^2+(2*d^2) • nodes A+(2*(a-d)*(a-2*d)/a) • g A

theorem cleanClockTest_apply (A : Fin s→Fin s→K) (a d : K) (r : Fin s) :
    cleanClockTest A a d r=
      nodes A r*(nodes A r-d)*(nodes A r-2*d)+(2*(a-d)*(a-2*d)/a)*g A r := by
  simp only [cleanClockTest,Pi.add_apply,Pi.sub_apply,Pi.pow_apply,Pi.smul_apply,smul_eq_mul]
  ring

theorem cleanClockTest_zero_off {a d : K} {i j r : Fin s} (D : GlobalNormal A a d i j)
    (off : g A r≠0) : cleanClockTest A a d r=0 := by
  rw [cleanClockTest_apply,D.base.origin.off_support r off,amplitude_value D.base.amplitude off]
  field_simp [D.base.origin.a_ne]
  ring

theorem cleanClockTest_action {a d : K} {i j : Fin s} (D : GlobalNormal A a d i j) (r : Fin s) :
    mat A (cleanClockTest A a d) r=(nodes A r)^2*(nodes A r-2*d)^2/4+
      ((a-2*d)^2/2)*g A r+(d/a)*(2*d-nodes A r)*h A r := by
  have rhs₂ := m2_relation D.base.q2 r
  have rhs₃ : M3 A r=(nodes A r)^4/4+(a^2/2)*g A r+((2*d^2-2*a^2)/a)*h A r-
      (d/a)*nodes A r*h A r := by
    have e := congrFun D.q3 r
    simp only [mDef_apply,Nat.reduceAdd,Nat.cast_ofNat,Pi.add_apply,Pi.smul_apply,Pi.sub_apply,
      smul_eq_mul,diag_apply] at e
    linear_combination e
  simp only [cleanClockTest,map_add,map_sub,map_smul,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  change M3 A r-(3*d)*M2 A r+(2*d^2)*M1 A r+(2*(a-d)*(a-2*d)/a)*h A r=_
  rw [rhs₃,rhs₂,m1_relation A r]
  dsimp only [twoLam]
  field_simp [D.base.origin.a_ne]
  ring

theorem new_clean_clock_h {A : Fin (s+1)→Fin (s+1)→K} {b : Vec K (s+1)}
    {a d : K} {i j : Fin (s+1)} (D : GlobalNormal A a d i j) (ha : StrictLower A)
    (ho : HasTreeOrderAtLeast A b p) (hp : 8≤p) (hN : (supportedNodes A (g A)).card=1) :
    ∃ r : Fin (s+1), g A r=0 ∧ nodes A r≠0 ∧ nodes A r≠d ∧ nodes A r≠2*d ∧ h A r≠0 := by
  have weight := single_off_weight_cancel D.base ho hN (by omega)
  have on5 := five_on_of_aggregate_zero ha ho hp weight
  let S : Set (Fin (s+1)) := {r | g A r=0 ∧ nodes A r≠0 ∧ nodes A r≠d ∧ nodes A r≠2*d}
  have ex : S.Nonempty := by
    by_contra n
    let T : Finset K := {0,d,2*d}
    have sub : onNodes A⊆T := by
      intro x hx
      obtain ⟨r,gr,rfl⟩ := mem_onNodes.mp hx
      by_contra! e
      have v : nodes A r≠0 ∧ nodes A r≠d ∧ nodes A r≠2*d := by simpa [T] using e
      exact n ⟨r,gr,v⟩
    have dT : T.card≤3 := (Finset.card_insert_le ..).trans (Nat.succ_le_succ
      ((Finset.card_insert_le ..).trans (by simp)))
    have c := (Finset.card_le_card sub).trans dT
    omega
  obtain ⟨r,hr,hm⟩ := wellFounded_lt.has_min S ex
  obtain ⟨g0,n0,nd,nt⟩ := show g A r=0 ∧ nodes A r≠0 ∧ nodes A r≠d ∧ nodes A r≠2*d from hr
  have pre (l : Fin (s+1)) (lr : l < r) : cleanClockTest A a d l=0 := by
    by_cases g0 : g A l=0
    · have h : nodes A l=0 ∨ nodes A l=d ∨ nodes A l=2*d := by
        by_contra! all
        exact hm l ⟨g0,all⟩ lr
      rcases h with h|h|h <;> simp [cleanClockTest_apply,g0,h]
    · exact cleanClockTest_zero_off D g0
  have e := cleanClockTest_action D r
  rw [causal_mat ha r _ pre,g0,mul_zero,add_zero] at e
  refine ⟨r,g0,n0,nd,nt,?_⟩
  intro z
  rw [z,mul_zero,add_zero] at e
  exact div_ne_zero (mul_ne_zero (pow_ne_zero 2 n0) (pow_ne_zero 2 (sub_ne_zero.mpr nt)))
    (by norm_num) e.symm

end RKCert.Paired.OneOff
