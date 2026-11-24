module

public import RKCert.Dirk15K1SignatureJoin
public import RKCert.Dirk15TwoEndedPivots

@[expose] public section

/-! # Two actual weighted and unweighted pivots for the surviving affine case

The first forward pivot is an original physical coordinate even if its
individual weight vanishes. The first reversed pivot earns a nonzero
weight and uses the true original terminal-zero marked test at grade
seven. There is no altered order certificate on a deleted tableau.
-/
namespace RKCert.Paired
open Module Polynomial RKCert.OneEscape RKCert.Endpoint RKCert.Paired.Signature
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [CharZero K]
variable {A : Fin 20→Fin 20→K} {b : Vec K 20}

namespace Order15K1Head.NativeMixedSignature
variable {h : Order15K1Head A b} {D : h.head.DeletedPencil} {v : Vec K 20}
variable (G : h.NativeMixedSignature D v)

structure TwoPivots where
  forward : Fin 20
  reverse : Fin 20
  f_nonterminal : forward≠Fin.last 19
  r_nonterminal : reverse≠Fin.last 19
  f_clock : nodes A forward≠0
  r_clock : mirror A reverse≠0
  r_active : b reverse≠0
  r_clean : v reverse=0
  f_omit : G.P.eval (nodes A forward)≠0
  r_omit : G.P.eval (nodes A reverse)≠0
  f_root : D.D.eval (nodes A forward)=0
  r_root : D.D.eval (nodes A reverse)=0
  f_diagonal : A forward forward=0
  r_diagonal : A reverse reverse=0
  f_one : paidMoment G.P (nodes A forward) 1=0
  f_two : paidMoment G.P (nodes A forward) 2=0
  r_one : paidMoment (reflectPolynomial G.P) (mirror A reverse) 1=0
  r_two : paidMoment (reflectPolynomial G.P) (mirror A reverse) 2=0

set_option maxHeartbeats 1600000 in
theorem true_two_pivots (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (H : Order15MinimalMarkedChart A b) (hm : finrank K (marked A 15 4)=2)
    (hv : v∈zeroSpace A 4) : Nonempty G.TwoPivots := by
  let P := G.P
  let c := nodes A
  let w := h.head.w
  let g : Vec K 20 := fun i => if i∈ghostPositions A b then P.eval (c i)-v i else 0
  let θ := evalNodes A P-g-v
  have gg : g∈simultaneousGhosts A b := by
    apply simultaneousGhosts_mem.mpr
    refine ⟨by simp [g,mem_ghostPositions],fun i hi => ?_⟩
    have e : i∉ghostPositions A b := fun g => hi.elim
      (fun q => q (mem_ghostPositions.mp g).2.1) (fun q => q (mem_ghostPositions.mp g).2.2)
    simp [g,e]
  have g3 : g∈zeroSpace A 3 := by
    rw [h.pure_core,h.core_eq]
    exact gg
  have g4 := zeroSpace_mono A (by decide : 3≤4) g3
  have tr : OrdinaryTrace A 4 θ P :=
    ((OrdinaryTrace.scalar A G.P_degree).sub_pure g4).sub_pure hv
  have clean_forward (i : Fin 20) (it : i≠Fin.last 19)
      (iθ : diag (nodes A) θ i≠0) :
      P.eval (c i)≠0 ∧ D.D.eval (c i)=0 ∧ ∀ q∈zeroSpace A 7,q i=0 := by
    have ig : i∉ghostPositions A b := by
      intro m
      apply iθ
      simp [θ,g,m,diag_apply,c]
    have wi : w i=0 := by
      by_contra wn
      apply iθ
      have e : v i=P.eval (c i) := G.fit i it ig wn
      simp [θ,g,ig,diag_apply,c,e]
    have vi : v i=0 := by
      rw [G.amplitude i ig,show h.head.w i=0 from wi,zero_mul]
    have pn : P.eval (c i)≠0 := by
      intro e
      apply iθ
      simp [θ,g,ig,diag_apply,c,vi,e]
    have dn : D.D.eval (c i)=0 := by
      have e := G.relation i it ig
      rwa [show h.head.w i=0 from wi,zero_mul] at e
    refine ⟨pn,dn,fun q hq => ?_⟩
    obtain ⟨R,_,rep⟩ := h.read_tail (h.head.seven.le hq)
    simpa only [show h.head.w i=0 from wi,mul_zero] using rep i ig
  obtain ⟨i,it,i0,ip,id,ia,i1,i2⟩ :=
    order15_forward_quartic_cut ha ho H.terminal G.P_ne G.P_degree tr clean_forward
  have sameProfile (i : Fin 20) (nz : reverseCubic A b i≠0) : v i=P.eval (nodes A i) := by
    change v i=G.P.eval (nodes A i)
    rw [G.reflect,reflectPolynomial,eval_comp,eval_sub,eval_one,eval_X]
    exact G.marked_fit i nz
  have clean_reverse (j : Fin 20) (jt : j≠Fin.last 19) (jb : b j≠0) (jv : v j=0)
      (p : P.eval (c j)≠0) : D.D.eval (c j)=0 := by
    have jg : j∉ghostPositions A b := fun e => jb (mem_ghostPositions.mp e).2.1
    have jw : w j=0 := by
      by_contra wn
      have r : v j=P.eval (c j) := G.fit j jt jg wn
      rw [jv,eq_comm] at r
      exact p r
    have e := G.relation j jt jg
    rwa [show h.head.w j=0 from jw,zero_mul] at e
  obtain ⟨j,jt,j0,jb,jv,jp,jd,ja,j1,j2⟩ := order15_reverse_quartic_cut ha ho H hm
    (order15_minimal_reverse_nonlocal ha ho H) G.P_ne G.P_degree hv sameProfile clean_reverse
  exact ⟨⟨i,j,it,jt,i0,j0,jb,jv,ip,jp,id,jd,ia,ja,i1,i2,j1,j2⟩⟩

theorem TwoPivots.affine_gram_gate {G : h.NativeMixedSignature D v} (T : G.TwoPivots) (nodiv : ¬G.P∣D.D) :
    ∃ R : K[X], R≠0 ∧ R.natDegree≤3 ∧ G.P=G.S*R ∧ R∣D.D ∧
      (paidMoment R (nodes A T.forward) 1*paidMoment R (nodes A T.forward) 3-
        (paidMoment R (nodes A T.forward) 2)^2=0) ∧
      (paidMoment (reflectPolynomial R) (mirror A T.reverse) 1 *
        paidMoment (reflectPolynomial R) (mirror A T.reverse) 3-
        (paidMoment (reflectPolynomial R) (mirror A T.reverse) 2)^2=0) :=
  two_ended_gram_of_mixed D.D G.R G.S G.P G.P_ne G.S_ne G.S_degree G.P_degree G.algebra nodiv
    T.f_one T.f_two T.r_one T.r_two

end Order15K1Head.NativeMixedSignature
end
end RKCert.Paired
