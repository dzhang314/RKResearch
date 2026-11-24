module

public import RKCert.Dirk15OrdinaryGhosts
public import RKCert.Dirk15SignatureAlgebra

@[expose] public section

/-! # Literal nonterminal signatures, with at most two per clock
These deductions do not assume distinct abscissae. The one-clock
surjectivity used here is only a consequence of the paid reverse orbit,
and the retained U-zero head decomposition is a separate premise. -/
namespace RKCert.Paired
open RKCert.Endpoint RKCert.OneEscape Polynomial
open scoped Classical

variable {K : Type*} [Field K] [CharZero K]
variable {A : Fin 20 → Fin 20 → K} {b : Vec K 20}

theorem order15_no_local_marked_row (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (h : Order15MinimalMarkedChart A b)
    (hfirst : ¬(markedTerminalZero (s:=19) A 15 3).map (diag (mirror A))≤
      markedTerminalZero (s:=19) A 15 3) {d : Vec K 20}
    (hd : d∈markedTerminalZero (s:=19) A 15 7) (z : K)
    (loc : ∀ i, mirror A i≠z → d i=0) : d=0 := by
  rw [order15_minimal_cubic_orbit ha ho h hfirst 7 (by decide) (by decide)] at hd
  have hp : d∈(⊥ : Submodule K (Vec K 20)) :=
    Clock.localized_mem (by simp) (fun a h => by simpa using h)
      (order15_minimal_cubic_sites ha ho h hfirst) hd loc
  simpa using hp

/-- Inside any single physical clock fiber, no nonzero linear relation
on the evaluation of true E7 is supported away from the last stage. -/
theorem order15_no_local_e7_relation (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (h : Order15MinimalMarkedChart A b)
    (hfirst : ¬(markedTerminalZero (s:=19) A 15 3).map (diag (mirror A))≤
      markedTerminalZero (s:=19) A 15 3) {d : Vec K 20}
    (hd : ∀ v∈treeSpace A 7,row d v=0) (ht : d (Fin.last 19)=0) (z : K)
    (loc : ∀ i, nodes A i≠z → d i=0) : d=0 := by
  apply order15_no_local_marked_row ha ho h hfirst (z:=1-z)
  · exact ⟨mem_annih.mpr hd,prior_last_iff.mpr ht⟩
  · intro i hi
    apply loc i
    intro he
    exact hi (by simp [mirror,he])

/-- The distinctness and fiber cap paid by a true E7 head expansion. The
two retained signatures at one clock are generally not the same row. -/
theorem order15_actual_signatures (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (h : Order15MinimalMarkedChart A b)
    (hfirst : ¬(markedTerminalZero (s:=19) A 15 3).map (diag (mirror A))≤
      markedTerminalZero (s:=19) A 15 3)
    {r n : ℕ} {U : Submodule K (Vec K 20)} {w : Vec K 20}
    (sh : zeroSpace A 7≤chain (diag (nodes A)) U w r)
    (idx : Fin n → Fin 20) (idx_inj : Function.Injective idx)
    (idx_nonterminal : ∀ i, idx i≠Fin.last 19)
    (core_zero : ∀ u∈U,∀ i,u (idx i)=0) :
    Function.Injective (fun i => (nodes A (idx i),w (idx i))) ∧
      ∀ z, (Signature.fiberAt (fun i => nodes A (idx i)) z).card≤2 := by
  classical
  let unit : Fin 20 → Vec K 20 := fun i => Pi.single i 1
  have u_at (i : Fin 20) : unit i i=1 := by simp [unit]
  have u_ne (i j : Fin 20) (hne : j≠i) : unit i j=0 := by simp [unit,Pi.single_eq_of_ne hne]
  have test (v : Vec K 20) (hv : v∈treeSpace A 7) (z : K) :
      ∃ α β : K, ∀ i, nodes A (idx i)=z → v (idx i)=α+β*w (idx i) := by
    obtain ⟨P,hP,hf⟩ := exists_poly_zeroSpace_charZero A hv
    obtain ⟨u,hu,Q,_,hvq⟩ := Clock.exists_head_poly (sh hf)
    refine ⟨P.eval z,Q.eval z,fun i hi => ?_⟩
    have h := hvq (idx i)
    simp only [Pi.sub_apply,evalNodes_apply,hi,core_zero u hu i,zero_add] at h
    linear_combination h
  have rel (d : Vec K 20) (hd : ∀ v∈treeSpace A 7,row d v=0) (z : K)
      (ht : d (Fin.last 19)=0) (loc : ∀ i,nodes A i≠z → d i=0) :
      d=0 := order15_no_local_e7_relation ha ho h hfirst hd ht z loc
  have inj : Function.Injective (fun i => (nodes A (idx i),w (idx i))) := by
    intro i j he
    by_contra! hne
    have hne' : idx i≠idx j := fun eq => hne (idx_inj eq)
    have hc : nodes A (idx i)=nodes A (idx j) := congrArg Prod.fst he
    have hw : w (idx i)=w (idx j) := congrArg Prod.snd he
    let d := unit (idx i)-unit (idx j)
    have hz := rel d (fun v hv => ?_) (nodes A (idx i)) (by
      simp only [d,Pi.sub_apply,u_ne _ _ (idx_nonterminal i).symm,
        u_ne _ _ (idx_nonterminal j).symm,sub_self]) ?_
    · have he := congrFun hz (idx i)
      simp [d,u_at,u_ne _ _ hne'] at he
    · obtain ⟨α,β,ht⟩ := test v hv (nodes A (idx i))
      have hi := ht i rfl
      have hj := ht j hc.symm
      change rowL d v=0
      rw [show rowL d=rowL (unit (idx i))-rowL (unit (idx j)) from map_sub _ _ _]
      rw [LinearMap.sub_apply,rowL_apply,rowL_apply,row_single_left,row_single_left,hi,hj,hw,sub_self]
    · intro k hk
      have hki : k≠idx i := fun e => hk (e ▸ rfl)
      have hkj : k≠idx j := fun e => hk (e.symm ▸ hc.symm)
      simp [d,u_ne _ _ hki,u_ne _ _ hkj]
  refine ⟨inj,fun z => ?_⟩
  by_contra! he
  obtain ⟨i,j,k,hi,hj,hk,hij,hik,hjk⟩ := Finset.two_lt_card_iff.mp he
  have ci : nodes A (idx i)=z := by simpa [Signature.fiberAt] using hi
  have cj : nodes A (idx j)=z := by simpa [Signature.fiberAt] using hj
  have ck : nodes A (idx k)=z := by simpa [Signature.fiberAt] using hk
  let a := w (idx i)
  let b' := w (idx j)
  let c := w (idx k)
  have hab : a≠b' := fun e => hij (inj (Prod.ext (ci.trans cj.symm) e))
  let d : Vec K 20 := (b'-c) • unit (idx i)+(c-a) • unit (idx j)+(a-b') • unit (idx k)
  have hz := rel d (fun v hv => ?_) z (by
    simp only [d,Pi.add_apply,Pi.smul_apply,smul_eq_mul,u_ne _ _ (idx_nonterminal i).symm,
      u_ne _ _ (idx_nonterminal j).symm,u_ne _ _ (idx_nonterminal k).symm,mul_zero,add_zero]) ?_
  · apply hab
    have e := congrFun hz (idx k)
    have hki : idx k≠idx i := fun e => hik (idx_inj e.symm)
    have hkj : idx k≠idx j := fun e => hjk (idx_inj e.symm)
    simpa [d,u_at,u_ne _ _ hki,u_ne _ _ hkj,sub_eq_zero] using e
  · obtain ⟨α,β,ht⟩ := test v hv z
    change rowL d v=0
    simp only [d,map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul,
      rowL_apply,row_single_left,unit,ht i ci,ht j cj,ht k ck,a,b',c]
    ring
  · intro l hl
    have hli : l≠idx i := fun e => hl (e.symm ▸ ci)
    have hlj : l≠idx j := fun e => hl (e.symm ▸ cj)
    have hlk : l≠idx k := fun e => hl (e.symm ▸ ck)
    simp [d,u_ne _ _ hli,u_ne _ _ hlj,u_ne _ _ hlk]

end RKCert.Paired
