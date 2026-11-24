module

public import RKCert.ERKOrderNineOneOffTailPrefix

@[expose] public section

/-! # The eighth and ninth physical stages are new on abscissas -/
namespace RKCert.Paired.OneOff.Seven
open Polynomial Module
open scoped Classical

variable {K : Type*} [Field K] [CharZero K] {A : Fin 12→Fin 12→K} {b : Vec K 12}

def IsNewOn (A : Fin 12→Fin 12→K) (d z : K) (r : Fin 12) : Prop :=
  g A r=0 ∧ nodes A r≠0 ∧ nodes A r≠d ∧ nodes A r≠2*d ∧ nodes A r≠z

theorem next_on_after_two_fibres (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 9)
    (oneOff : (supportedNodes A (g A)).card=1)
    {a d : K} {i j r : Fin 12} (D : GlobalNormal A a d i j) (F : FirstFour A a d (by decide))
    (D7 : TwoFibres A a d (nodes A (5:Fin 12)))
    (r6 : (6:Fin 12)<r) (rne : r≠Fin.last 11)
    (ind : IndependentBefore (treeSpace A 4) r) :
    IsNewOn A d (nodes A (5:Fin 12)) r := by
  let x := nodes A r
  let z := nodes A (5:Fin 12)
  have an := D.base.origin.a_ne
  have dn := D.base.dn
  have C4 := order9_clean_four ha ho oneOff D F
  obtain ⟨rk,rangeEq,_,_⟩ := order9_maximal_normal_profile ha ho oneOff D F
  have f0 : nodes A (0:Fin 12)=0 ∧ g A (0:Fin 12)=0 := by
    have e := F.features 0
    simpa [chartNode,chartDefect] using And.intro e.1 e.2.1
  have sixth := order9_sixth_feature ha ho oneOff D F
  have zn : z≠0 := sixth.2.1
  have zd : z≠d := sixth.2.2.1
  have zt : z≠2*d := sixth.2.2.2.1
  obtain ⟨L,_,shape⟩ := ordinary_curve D7 dn zn zt
  have gr : g A r=0 := by
    by_contra off
    exact off_repeats_first ha ho oneOff D F rk rangeEq ind ((by decide : (1:Fin 12)<6).trans r6) off
  have nt : x≠2*d := by
    intro nc
    have hn : h A (4:Fin 12)≠h A (3:Fin 12) :=
      fun e=>C4.diff (by rw [scaledH_eval,scaledH_eval,e])
    exact no_further_on_same_clock ha ho rk rangeEq ind
      ((by decide : (3:Fin 12)<6).trans r6) ((by decide : (4:Fin 12)<6).trans r6)
      (C4.node3.trans nc.symm) (C4.node4.trans nc.symm) C4.g3 C4.g4 gr hn
  have nz : x≠z := by
    intro nc
    have hn : h A (6:Fin 12)≠h A (5:Fin 12) :=
      fun e=>D7.Hdiff (by rw [scaledH_eval,scaledH_eval,e])
    exact no_further_on_same_clock ha ho rk rangeEq ind ((by decide : (5:Fin 12)<6).trans r6) r6
      (C4.node5.trans nc.symm) (D7.node7.trans nc.symm) C4.g5 D7.g7 gr hn
  have H := shape r rne gr nt nz
  have n0 : x≠0 := by
    intro nc
    have f := shape (0:Fin 12) (by decide) f0.2
      (by rw [f0.1]; exact (mul_ne_zero (by norm_num : (2:K)≠0) dn).symm)
      (by rw [f0.1]; exact zn.symm)
    have hh : scaledH A a (0:Fin 12)=scaledH A a r := by
      rw [f,H,f0.1]
      exact congrArg L.eval nc.symm
    rw [scaledH_eval,scaledH_eval] at hh
    exact order9_no_repeated_feature ha ho rk rangeEq ind ((by decide : (0:Fin 12)<6).trans r6)
      (f0.1.trans nc.symm) (f0.2.trans gr.symm) ((div_left_inj₀ an).mp hh)
  have nd : x≠d := by
    intro nc
    have f := shape (2:Fin 12) (by decide) C4.g2
      (by rw [C4.node2]; intro e; exact dn (by linear_combination -e))
      (by rw [C4.node2]; exact zd.symm)
    have hh : scaledH A a (2:Fin 12)=scaledH A a r := by
      rw [f,H,C4.node2]
      exact congrArg L.eval nc.symm
    rw [scaledH_eval,scaledH_eval] at hh
    exact order9_no_repeated_feature ha ho rk rangeEq ind ((by decide : (2:Fin 12)<6).trans r6)
      (C4.node2.trans nc.symm) (C4.g2.trans gr.symm) ((div_left_inj₀ an).mp hh)
  exact ⟨gr,n0,nd,nt,nz⟩

theorem order9_last_two_new_on (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 9)
    (oneOff : (supportedNodes A (g A)).card=1)
    {a d : K} {i j : Fin 12} (D : GlobalNormal A a d i j) (F : FirstFour A a d (by decide))
    (D7 : TwoFibres A a d (nodes A (5:Fin 12))) :
    IsNewOn A d (nodes A (5:Fin 12)) (7:Fin 12) ∧
      IsNewOn A d (nodes A (5:Fin 12)) (8:Fin 12) ∧ nodes A (8:Fin 12)≠nodes A (7:Fin 12) := by
  let z := nodes A (5:Fin 12)
  let f := physicalTail A a d z
  have I7 := order9_first_seven_independent ha ho oneOff D F D7
  have row8 := next_on_after_two_fibres ha ho oneOff D F D7 (by decide) (by decide) I7
  have f8 : f (7:Fin 12)≠0 := by
    rw [show f=physicalTail A a d z from rfl,physicalTail_on a d z row8.1,tailPoly_eval]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero row8.2.1 (sub_ne_zero.mpr row8.2.2.1))
      (sub_ne_zero.mpr row8.2.2.2.1)) (sub_ne_zero.mpr row8.2.2.2.2)
  have I8 := extend_independent_before (j:=(7:Fin 12)) (r:=(8:Fin 12)) rfl I7
    (physicalTail_mem A a d z) (order9_tail_initial_zero ha ho oneOff D F D7) f8
  have row9 := next_on_after_two_fibres ha ho oneOff D F D7 (by decide) (by decide) I8
  refine ⟨row8,row9,?_⟩
  intro e
  obtain ⟨rk,rangeEq,_,_⟩ := order9_maximal_normal_profile ha ho oneOff D F
  have sixth := order9_sixth_feature ha ho oneOff D F
  obtain ⟨L,_,curve⟩ := ordinary_curve D7 D.base.dn sixth.2.1 sixth.2.2.2.1
  have f := curve (7:Fin 12) (by decide) row8.1 row8.2.2.2.1 row8.2.2.2.2
  have q := curve (8:Fin 12) (by decide) row9.1 row9.2.2.2.1 row9.2.2.2.2
  have hh : scaledH A a (7:Fin 12)=scaledH A a (8:Fin 12) := by rw [f,q,e]
  rw [scaledH_eval,scaledH_eval] at hh
  exact order9_no_repeated_feature ha ho rk rangeEq I8 (by decide)
    e.symm (row8.1.trans row9.1.symm) ((div_left_inj₀ D.base.origin.a_ne).mp hh)

end RKCert.Paired.OneOff.Seven
