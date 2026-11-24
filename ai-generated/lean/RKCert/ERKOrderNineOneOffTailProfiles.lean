module

public import RKCert.ERKOrderNineOneOffSeventhActions

@[expose] public section

/-! # The fifth and sixth tree spaces in physical polynomial coordinates -/
namespace RKCert.Paired.OneOff.Seven
open Polynomial Module
open scoped Classical

variable {K : Type*} [Field K] [CharZero K] {A : Fin 12→Fin 12→K} {b : Vec K 12}

def TailProfile (A : Fin 12→Fin 12→K) (a : K) (n : ℕ) (v : Vec K 12) : Prop :=
  ∃ (P Q : K[X]) (β : K), P.natDegree≤n ∧ Q.natDegree≤n-3 ∧
    ∀ r, v r=P.eval (nodes A r)+β*g A r+scaledH A a r*Q.eval (nodes A r)

theorem native_profile_five {a : K} (an : a≠0)
    (eq : LinearMap.range (normalProfileMap A)=treeSpace A 5) {v : Vec K 12}
    (vv : v∈treeSpace A 5) : TailProfile A a 5 v := by
  rw [←eq] at vv
  obtain ⟨w,rfl⟩ := vv
  refine ⟨ofFn 6 w.1,C a*ofFn 3 w.2.2,w.2.1,
    Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) _),
    (natDegree_C_mul_le _ _).trans (Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) _)),?_⟩
  intro r
  rw [normal_profile_value,scaledH_eval,eval_mul,eval_C]
  field_simp [an]
  ring

theorem profile_add_clock {a : K} {u v : Vec K 12}
    (gc : diag (nodes A) (g A)=a • g A)
    (hu : TailProfile A a 5 u) (hv : TailProfile A a 5 v) :
    TailProfile A a 6 (u+diag (nodes A) v) := by
  obtain ⟨P,Q,β,Pd,Qd,pu⟩ := hu
  obtain ⟨P',Q',β',Pd',Qd',pv⟩ := hv
  refine ⟨P+X*P',Q+X*Q',β+a*β',?_,?_,?_⟩
  · exact natDegree_add_le_of_le (Pd.trans (by decide : 5≤6))
      (natDegree_mul_le_of_le (show (X:K[X]).natDegree≤1 by simp) Pd')
  · exact natDegree_add_le_of_le (Qd.trans (by decide : 5-3≤6-3))
      (natDegree_mul_le_of_le (show (X:K[X]).natDegree≤1 by simp) Qd')
  · intro r
    simp only [Pi.add_apply,diag_apply,eval_add,eval_mul,eval_X,pu r,pv r]
    have e := congrFun gc r
    simp only [diag_apply,Pi.smul_apply,smul_eq_mul] at e
    linear_combination β'*e

theorem order9_treeSpace_six_clock_sup (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 9)
    (rk : finrank K (treeSpace A 5)=10) :
    treeSpace A 6=treeSpace A 5⊔(treeSpace A 5).map (diag (nodes A)) := by
  let V := treeSpace A 5
  let W := V ⊔ V.map (diag (nodes A))
  have bound := (order9_twelve_stage_chart ha ho).2.2.2.2.2.2.2
  have wn : ¬ V.map (diag (nodes A))≤V := order9_treeSpace_five_not_clock_invariant ha ho
  have lt : V < W := lt_of_le_of_ne le_sup_left (fun h =>
    wn ((show V.map (diag (nodes A))≤W from le_sup_right).trans h.ge))
  have gr := Submodule.finrank_lt_finrank_of_lt lt
  have incl : W≤treeSpace A 6 := sup_le (treeSpace_mono A (by decide)) (by
    rintro _ ⟨z,hz,rfl⟩
    exact diag_treeSpace A 5 hz)
  exact (Submodule.eq_of_le_of_finrank_le incl (by change finrank K V=10 at rk; omega)).symm

theorem order9_native_profiles (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 9)
    (oneOff : (supportedNodes A (g A)).card=1)
    {a d : K} {i j : Fin 12} (D : GlobalNormal A a d i j) (F : FirstFour A a d (by decide)) :
    (∀ v∈treeSpace A 5, TailProfile A a 5 v) ∧
      (∀ v∈treeSpace A 6, TailProfile A a 6 v) := by
  obtain ⟨rk,eq,_,_⟩ := order9_maximal_normal_profile ha ho oneOff D F
  have five (v : Vec K 12) (vm : v∈treeSpace A 5) : TailProfile A a 5 v :=
    native_profile_five D.base.origin.a_ne eq vm
  refine ⟨five,?_⟩
  intro v hv
  rw [order9_treeSpace_six_clock_sup ha ho rk] at hv
  obtain ⟨u,um,_,⟨w,wm,rfl⟩,rfl⟩ := Submodule.mem_sup.mp hv
  exact profile_add_clock D.base.origin.g_clock (five u um) (five w wm)

end RKCert.Paired.OneOff.Seven
