module

public import RKCert.ReviewedNative.OneOffFirstH
public import RKCert.ReviewedNative.PolynomialStageSeparation

@[expose] public section

namespace RKResearch.Certified.Graded.OneOff
open Module Polynomial
open scoped Classical Matrix

variable {K : Type*} [Field K] [CharZero K] {s : ℕ}
variable {A : Matrix (Fin s) (Fin s) K}

noncomputable abbrev k (A : Matrix (Fin s) (Fin s) K) : Fin s → K := mat A (h A)

omit [CharZero K] in
theorem causal_action_eq (ha : ∀ i j, i ≤ j → A i j = 0) (i : Fin s) (v w : Fin s → K)
    (hpre : ∀ j, j < i → v j=w j) : mat A v i=mat A w i := by
  have e := causal_mat ha i (v-w) (fun j hj => by simp [hpre j hj])
  simpa only [map_sub,Pi.sub_apply,sub_eq_zero] using e

omit [CharZero K] in
theorem clock_power_action (ha : ∀ i j, i ≤ j → A i j = 0) {a : K} {i : Fin s} (n : ℕ)
    (pre : ∀ j, j < i → nodes A j=0 ∨ nodes A j=a) :
    mat A ((nodes A)^(n+1)) i=a^n*mat A (nodes A) i := by
  have eq := causal_action_eq ha i ((nodes A)^(n+1)) (a^n • nodes A) (fun j hj => by
    rw [Pi.pow_apply,Pi.smul_apply,smul_eq_mul]
    rcases pre j hj with h0|ha'
    · simp [h0]
    · simp [ha',pow_succ])
  simpa only [map_smul,Pi.smul_apply,smul_eq_mul] using eq

theorem not_invariant_with_g (ha : ∀ i j, i ≤ j → A i j = 0) {n : ℕ}
    (hsep : PolySeparated A n) (hn : 1≤n) {U : Submodule K (Fin s → K)}
    (hU : U≤zeroSpace A n) (gm : g A∈U)
    (hA : ∀ v∈U, mat A v∈U) (hC : ∀ v∈U, diag (nodes A) v∈U) : False := by
  have e : diag (nodes A) (1:Fin s → K)=nodes A := by ext j; simp
  apply hsep.nodes_not_mem hn
  apply hU
  rw [←e]
  apply mem_of_invariant_seed (Equiv.refl _) (mat A) (causal_mat ha) (nodes A) 1 U hA hC
  rw [forward_seed_eq]
  exact U.smul_mem _ gm

omit [CharZero K] in
theorem extra_rank_three_span (rank3 : finrank K (zeroSpace A 3)=2)
    (rank4 : finrank K (zeroSpace A 4)=3) {v : Fin s → K}
    (vm : v∈zeroSpace A 4) (out : v∉zeroSpace A 3) :
    zeroSpace A 4 = zeroSpace A 3 ⊔ Submodule.span K {v} := by
  have dim := Submodule.finrank_sup_span_singleton out
  symm
  apply Submodule.eq_of_le_of_finrank_le
    (sup_le (zeroSpace_mono _ (by decide)) ((Submodule.span_singleton_le_iff_mem ..).mpr vm))
  rw [rank4,dim,rank3]

omit [CharZero K] in
theorem rank_three_rep (e3 : zeroSpace A 3=Submodule.span K {g A, h A}) {v w : Fin s → K}
    (e4 : zeroSpace A 4=zeroSpace A 3 ⊔ Submodule.span K {v}) (wm : w∈zeroSpace A 4) :
    ∃ α β γ : K, w=(α • g A+β • h A)+γ • v := by
  rw [e4] at wm
  obtain ⟨w₃,h₃,w₄,h₄,rfl⟩ := Submodule.mem_sup.mp wm
  rw [e3] at h₃
  obtain ⟨α,β,rfl⟩ := Submodule.mem_span_pair.mp h₃
  obtain ⟨γ,rfl⟩ := Submodule.mem_span_singleton.mp h₄
  exact ⟨α,β,γ,rfl⟩

theorem coefficient_of_first_g {a : K} {i : Fin s} (ha : ∀ i j, i ≤ j → A i j = 0)
    (O : Origin A a i) {ξ μ ν : K} {v : Fin s → K} (vi : v i=0)
    (eq : mDef A 3=(ξ • g A+μ • h A)+ν • v) : ξ=a^2/2 := by
  have e := congrFun eq i
  have ep := O.mDef_first ha (j:=3) (by decide)
  simp only [ep,Pi.add_apply,Pi.smul_apply,smul_eq_mul,O.defect,O.h_first ha,
    vi,mul_zero,add_zero,Nat.reduceAdd,Nat.cast_ofNat] at e
  apply mul_right_cancel₀ (div_ne_zero (neg_ne_zero.mpr (pow_ne_zero 2 O.a_ne))
    (by norm_num) : -a^2/2 ≠ 0)
  linear_combination -e

/-- Beginning of Case I of the amplitude proof. In this branch a
nonconstant amplitude forces a precise, globally valid scalar relation
and the cubic defect's coefficient on (Ag). -/
structure CaseI (A : Matrix (Fin s) (Fin s) K) (a v nu : K) : Prop where
  v_ne : v≠0
  v_changed : v≠ -a^2/2
  law : ∀ i, 2*v*h A i= -a*g A i*(g A i+a^2/2)
  on_zero : ∀ i, g A i=0 → h A i=0
  q2 : mDef A 2=(2*a/3) • g A+(-2/3:K) • h A
  q3 : mDef A 3=((a^2/2) • g A+(-a) • h A)+nu • k A

theorem caseI_of_nonconstant (ha : ∀ i j, i ≤ j → A i j = 0) (hsep : PolySeparated A 4)
    (rank3 : finrank K (zeroSpace A 3)=2) (rank4 : finrank K (zeroSpace A 4)=3)
    {a lam : K} {i j : Fin s} (O : Origin A a i)
    (e3 : zeroSpace A 3=Submodule.span K {g A, h A})
    (qform : mDef A 2=(2*a/3) • g A+lam • h A) (F : FirstH A a lam j)
    (sq3 : (g A)^2∈zeroSpace A 3) (nc : (g A)^2≠(-a^2/2) • g A) :
    ∃ v nu, CaseI A a v nu := by
  rw [e3] at sq3
  obtain ⟨α,β,eq⟩ := Submodule.mem_span_pair.mp sq3
  have ai : α= -a^2/2 := by
    have eqi := congrFun eq.symm i
    simp only [Pi.pow_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul,
      O.defect,O.h_first ha,add_zero,mul_zero] at eqi
    apply mul_right_cancel₀ (div_ne_zero (neg_ne_zero.mpr (pow_ne_zero 2 O.a_ne))
      (by norm_num) : -a^2/2 ≠ 0)
    linear_combination -eqi
  subst α
  have bn : β≠0 := by intro z; apply nc; simpa [z] using eq.symm
  have at_ (z : Fin s) : (g A z)^2=(-a^2/2)*g A z+β*h A z := by
    simpa only [Pi.pow_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul] using congrFun eq.symm z
  have hon (z : Fin s) (g0 : g A z=0) : h A z=0 := by
    have e := at_ z
    simp only [g0,zero_pow (by decide : 2≠0),mul_zero,zero_add] at e
    exact (mul_eq_zero.mp e.symm).resolve_left bn
  have hclock : diag (nodes A) (h A)=a • h A := by
    ext z
    by_cases g0 : g A z=0
    · simp only [diag_apply,Pi.smul_apply,smul_eq_mul,hon z g0,mul_zero]
    · simp [diag_apply,O.off_support z g0]
  have ko : k A∉zeroSpace A 3 := by
    intro km
    have gm : g A∈zeroSpace A 3 := zeroSpace_mono A (by decide) (mDef_mem A 1)
    have hm : h A∈zeroSpace A 3 := mat_zeroSpace_charZero A 2 (mDef_mem A 1)
    apply not_invariant_with_g ha (hsep.mono (by decide : 3≤4)) (by decide)
      le_rfl gm
    · intro u hu
      rw [e3] at hu
      obtain ⟨c,d,rfl⟩ := Submodule.mem_span_pair.mp hu
      rw [map_add,map_smul,map_smul]
      exact (zeroSpace A 3).add_mem ((zeroSpace A 3).smul_mem _ hm)
        ((zeroSpace A 3).smul_mem _ km)
    · intro u hu
      rw [e3] at hu
      obtain ⟨c,d,rfl⟩ := Submodule.mem_span_pair.mp hu
      rw [map_add,map_smul,map_smul,O.g_clock,hclock]
      exact (zeroSpace A 3).add_mem ((zeroSpace A 3).smul_mem _ ((zeroSpace A 3).smul_mem _ gm))
        ((zeroSpace A 3).smul_mem _ ((zeroSpace A 3).smul_mem _ hm))
  have km : k A∈zeroSpace A 4 :=
    mat_zeroSpace_charZero A 3 (mat_zeroSpace_charZero A 2 (mDef_mem A 1))
  have r3 := extra_rank_three_span rank3 rank4 km ko
  obtain ⟨ξ,μ,ν,eq3⟩ := rank_three_rep e3 r3 (mDef_mem A 3)
  have ki : k A i=0 := causal_mat ha i _ (fun z hz =>
    causal_mat ha z _ (fun w hw => O.earlier_defect w (hw.trans hz)))
  have ξ' := coefficient_of_first_g ha O ki eq3
  subst ξ
  rcases F.alternative with ⟨gz,_,_,_⟩|⟨gv,vc,cj,hj,lj⟩
  · exact (F.nonzero (hon j gz)).elim
  let v := g A j
  change v≠0 at gv
  change v≠ -a^2/2 at vc
  change h A j= -a*(v+a^2/2)/2 at hj
  have hβ : β*a= -2*v := by
    apply mul_right_cancel₀ (show v+a^2/2 ≠ 0 from fun zz => vc (by linear_combination zz))
    have jj := at_ j
    change v^2=(-a^2/2)*v+β*h A j at jj
    rw [hj] at jj
    linear_combination 2*jj
  have law (z : Fin s) : 2*v*h A z= -a*g A z*(g A z+a^2/2) := by
    linear_combination a*(at_ z)+h A z*hβ
  have kj : k A j=0 := causal_mat ha j _ F.earlier
  have cpre : ∀ z, z < j → nodes A z=0 ∨ nodes A z=a := by
    intro z hz
    rcases F.prefix_features z hz with e|e
    · exact Or.inl e.1
    · exact Or.inr e.1
  have ac : mat A (nodes A) j = a^2/2+v := by
    have e := g_apply A j
    rw [cj] at e
    linear_combination -e
  have act := clock_power_action ha (n:=2) cpre
  have e := congrFun eq3 j
  rw [mDef_apply,act,ac,cj] at e
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,kj,mul_zero,add_zero,
    Nat.reduceAdd,Nat.cast_ofNat] at e
  change a^2*(a^2/2+v)-a^4/4=(a^2/2)*v+μ*h A j at e
  have μ' : μ= -a := by
    apply mul_right_cancel₀ F.nonzero
    linear_combination -e + a*hj
  subst μ
  exact ⟨v,ν,⟨gv,vc,law,hon,lj ▸ qform,eq3⟩⟩

end RKResearch.Certified.Graded.OneOff
