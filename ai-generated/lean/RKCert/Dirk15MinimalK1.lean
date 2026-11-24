module

public import RKCert.Dirk15PaidProductScalars
public import RKCert.Dirk15DeletedPencilJacobi
public import RKCert.Dirk15MinimalMovingQuartic
public import RKCert.Dirk15GhostPositions
public import RKCert.Dirk15PhysicalSignatures
public import RKCert.Dirk15HiddenSignatureArrays

@[expose] public section

/-! # The actual one-dimensional core and its four mixed grade-ten products -/
namespace RKCert.Paired
open Module Polynomial RKCert.OneEscape RKCert.Endpoint
open Order15MinimalHead.DeletedPencil
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [CharZero K]
variable {A : Fin 20 → Fin 20 → K} {b : Vec K 20}

theorem Order15MinimalHead.unfolded_sites (h : Order15MinimalHead A b)
    (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15) (H : Order15MinimalMarkedChart A b)
    (unfolded : deleteTerminal K 19 (((diag (nodes A))^h.length) h.w)∉deletedTreeSpace A 7) :
    h.length+4≤(Clock.headSites (deleteTerminal K 19 (nodes A)) (deleteTerminal K 19 h.w)).card := by
  let c := deleteTerminal K 19 (nodes A)
  let w := deleteTerminal K 19 h.w
  let U := h.U.map (deleteTerminal K 19)
  let L := deletedHeadOrbit A h.U h.w (h.length+4)
  let S := deletedScalarOrbit A 7
  have form : deletedTreeSpace A 11=S⊔L := by
    rcases h.deleted_growth_dichotomy ha ho H with ⟨e,_⟩|⟨_,band⟩
    · exact (unfolded e).elim
    · exact band 4 (by decide)
  have ed := (order15_minimal_deleted_band ha ho H 11 (by decide) (by decide)).2
  rw [form] at ed
  have hist := Submodule.finrank_sup_add_finrank_inf_eq S L
  rw [ed] at hist
  have scalar : finrank K S≤8 := Order15MinimalHead.deleted_scalar_rank_upper 7
  have core : finrank K U≤finrank K h.U := Submodule.finrank_map_le _ _
  have tail : finrank K L≤finrank K U+(Clock.headSites c w).card :=
    chain_dim_sites (c:=c) (w:=w) (U:=U) _
  have len := h.length_sum
  change h.length+4≤(Clock.headSites c w).card
  omega

structure Order15K1Head (A : Fin 20 → Fin 20 → K) (b : Vec K 20) where
  head : Order15MinimalHead A b
  core_one : finrank K head.U=1
  core_eq : head.U=simultaneousGhosts A b
  pure_core : zeroSpace A 3=head.U
  head_zero : ∀ i∈ghostPositions A b,head.w i=0

omit [CharZero K] in
theorem Order15K1Head.length_five (h : Order15K1Head A b) : h.head.length=5 := by
  rw [Order15MinimalHead.length,h.core_one]

omit [CharZero K] in
theorem order15_k1_head (H : Order15MinimalMarkedChart A b) (h : Order15MinimalHead A b)
    (one : finrank K h.U=1) : Nonempty (Order15K1Head A b) := by
  let G := simultaneousGhosts A b
  have r3 := H.initial.f3
  have dg : finrank K G≤finrank K h.U := Submodule.finrank_mono h.ghosts
  have fg : finrank K (zeroSpace A 3)≤finrank K G := Submodule.finrank_mono h.cubic
  have gU : G=h.U := Submodule.eq_of_le_of_finrank_le h.ghosts (by omega)
  have fU : zeroSpace A 3=h.U :=
    Submodule.eq_of_le_of_finrank_le (h.cubic.trans h.ghosts) (by omega)
  let w : Vec K 20 := fun i=>if i∈ghostPositions A b then 0 else h.w i
  have diff : h.w-w∈h.U := by
    rw [←gU]
    apply simultaneousGhosts_mem.mpr
    refine ⟨by simp [w,mem_ghostPositions],fun i hi=>?_⟩
    have ni : i∉ghostPositions A b := fun e => hi.elim
      (fun q => q (mem_ghostPositions.mp e).2.1) (fun q => q (mem_ghostPositions.mp e).2.2)
    simp [w,ni]
  have band (r : ℕ) : chain (diag (nodes A)) h.U w r=chain (diag (nodes A)) h.U h.w r := by
    have e := chain_sub_head (w:=h.w) h.maximal.2.1 diff r
    simpa only [sub_sub_cancel] using e
  let j : Order15MinimalHead A b := ⟨h.U,w,h.maximal,h.low,h.high,h.ghosts,h.cubic,
    h.six.trans (band _).symm,h.seven.trans (band _).symm,h.seven_escape⟩
  exact ⟨⟨j,one,gU.symm,fU,fun i e=>by simp [j,w,e]⟩⟩

namespace Order15K1Head
variable (h : Order15K1Head A b)

omit [CharZero K] in
theorem paid_products {v : Vec K 20} (hv : v∈zeroSpace A 4) (i : Fin 4) :
    originalClockShift A (v*h.head.w) i.val∈zeroSpace A 10 := by
  let C' := diag (nodes A)
  let w := h.head.w
  have eq : zeroSpace A 6=chain C' h.head.U w 4 := by
    have e := h.head.six
    rwa [h.core_one] at e
  have head : (C'^i.val) w∈zeroSpace A 6 :=
    ((chain_le_iff _).mp eq.ge).2 i.val i.isLt
  have p : v*(C'^i.val) w∈zeroSpace A (4+6) := zeroSpace_mul hv head
  have form : originalClockShift A (v*w) i.val=v*(C'^i.val) w := by
    ext j
    change (C'^i.val) (v*w) j=v j*((C'^i.val) w) j
    simp only [C',Clock.pow_diag_apply,Pi.mul_apply]
    ring
  rw [form]
  exact p

omit [CharZero K] in
theorem read_tail {v : Vec K 20} {n : ℕ} (hv : v∈chain (diag (nodes A)) h.head.U h.head.w n) :
    ∃ T : K[X], (T=0 ∨ T.natDegree<n) ∧
      ∀ i : Fin 20,i∉ghostPositions A b → v i=T.eval (nodes A i)*h.head.w i := by
  obtain ⟨u,hu,T,td,eq⟩ := Clock.exists_head_poly hv
  refine ⟨T,?_,fun i ni=>?_⟩
  · by_cases e : T=0
    · exact Or.inl e
    · exact Or.inr ((natDegree_lt_iff_degree_lt e).mpr td)
  · have z := ghostPositions_vanish (v:=u) (h.core_eq ▸ hu) ni
    simpa only [z,zero_add] using eq i

theorem eighteen_indices (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (H : Order15MinimalMarkedChart A b) :
    ∃ idx : Fin 18→Fin 20, Function.Injective idx ∧
      (∀ i,idx i≠Fin.last 19 ∧ idx i∉ghostPositions A b) ∧
      (∀ i : Fin 20,i≠Fin.last 19→i∉ghostPositions A b→∃ j,idx j=i) ∧
      Function.Injective (fun i => (nodes A (idx i),h.head.w (idx i))) ∧
      ∀ a, (Signature.fiberAt (fun i => nodes A (idx i)) a).card≤2 := by
  have rn : 18=19-finrank K (simultaneousGhosts A b) := by rw [←h.core_eq,h.core_one]
  obtain ⟨idx,inji,ret,onto⟩ := exists_retained_nonghost_indices H.terminal.weight_ne rn
  have ⟨inj,cap⟩ := order15_actual_signatures ha ho H (order15_minimal_reverse_nonlocal ha ho H)
    h.head.seven.le idx inji (fun i => (ret i).1)
    (fun u hu i => ghostPositions_vanish (h.core_eq ▸ hu) (ret i).2)
  exact ⟨idx,inji,ret,onto,inj,cap⟩

set_option maxHeartbeats 1750000 in
theorem actual_mixed_polynomial (D : h.head.DeletedPencil) (ha : LowerArray A)
    (ho : HasTreeOrderAtLeast A b 15) (H : Order15MinimalMarkedChart A b)
    {v : Vec K 20} (hv : v∈zeroSpace A 4) :
    ∃ P : K[X],P.natDegree≤4 ∧ ∀ i : Fin 20,i≠Fin.last 19 → i∉ghostPositions A b →
      h.head.w i≠0 → v i=P.eval (nodes A i) := by
  let w := h.head.w
  let c := nodes A
  have pay (i : Fin 4) := h.paid_products hv i
  by_cases folded : deleteTerminal K 19 (((diag c)^h.head.length) w)∈deletedTreeSpace A 7
  · obtain ⟨S⟩ := D.folded_paid_shifts ha ho H folded pay
    have fold : deleteTerminal K 19 (((diag (nodes A))^h.head.length) h.head.w)∈deletedTreeSpace A 7 := folded
    have d7 := D.growth
    rw [ite_eq_left fold] at d7
    have z := S.folded_initial_four_zero d7
    obtain ⟨P,dP,rep⟩ := h.read_tail (S.paid 0)
    have d : P.natDegree≤4 := by
      rcases dP with e|e
      · simp [e]
      · rw [h.length_five] at e
        omega
    refine ⟨P,d,fun i nt ng wn=>mul_right_cancel₀ wn ?_⟩
    have e := deleteTerminal_eq_at_ne (S.decomposition 0) i nt
    change v i*w i=(S.poly 0).eval (c i)+S.tail 0 i at e
    simpa only [z,eval_zero,zero_add,rep i ng] using e
  · obtain ⟨S⟩ := D.unfolded_paid_shifts ha ho H folded pay
    have openHead : deleteTerminal K 19 (((diag (nodes A))^h.head.length) h.head.w)∉deletedTreeSpace A 7 := folded
    have d8 := D.growth
    rw [ite_eq_right openHead] at d8
    have z := S.unfolded_four_zero d8
    have p (i : Fin 4) := h.read_tail (S.paid i)
    choose T dT rep using p
    have d (i : Fin 4) : (T i).natDegree≤7 := by
      rcases dT i with e|e
      · simp [e]
      · rw [h.length_five] at e
        omega
    have step (i : Fin 3) : T i.succ=X*T i.castSucc := by
      let c' := deleteTerminal K 19 c
      let w' := deleteTerminal K 19 w
      let Z := Clock.headSites c' w'
      have sites := h.head.unfolded_sites ha ho H folded
      rw [h.length_five] at sites
      change 9≤Z.card at sites
      apply Polynomial.eq_of_degrees_lt_of_eval_finset_eq Z
      · exact degree_le_natDegree.trans_lt (by exact_mod_cast
          ((d i.succ).trans_lt (by omega : 7<Z.card)))
      · have a := natDegree_mul_le (p:=(X:K[X])) (q:=T i.castSucc)
        rw [natDegree_X] at a
        exact degree_le_natDegree.trans_lt (by exact_mod_cast
          (show (X*T i.castSucc).natDegree<Z.card by have :=d i.castSucc;omega))
      · intro a ha
        obtain ⟨j,jm,rfl⟩ := Finset.mem_image.mp ha
        let p := j.castSucc
        have wp : w p≠0 := (Finset.mem_filter.mp jm).2
        have gn : p∉ghostPositions A b := fun e => wp (h.head_zero p e)
        have nt : p≠Fin.last 19 := Fin.castSucc_ne_last j
        have f₁ := deleteTerminal_eq_at_ne (S.decomposition i.succ) p nt
        have f₀ := deleteTerminal_eq_at_ne (S.decomposition i.castSucc) p nt
        change ((diag c)^i.succ.val) (v*w) p=(S.poly i.succ).eval (c p)+S.tail i.succ p at f₁
        change ((diag c)^i.castSucc.val) (v*w) p=(S.poly i.castSucc).eval (c p)+S.tail i.castSucc p at f₀
        simp only [Clock.pow_diag_apply,z,eval_zero,zero_add,rep _ p gn] at f₁ f₀
        change (T i.succ).eval (c p)=(X*T i.castSucc).eval (c p)
        rw [eval_mul,eval_X]
        apply mul_right_cancel₀ wp
        change c p^(i.val+1)*(v*w) p=_ at f₁
        change c p^i.val*(v*w) p=_ at f₀
        rw [pow_succ'] at f₁
        linear_combination c p*f₀-f₁
    have eq₁ : T 1=X*T 0 := step 0
    have eq₂ : T 2=X*T 1 := step 1
    have eq₃ : T 3=X*T 2 := step 2
    have eq : T 3=X^3*T 0 := by rw [eq₃,eq₂,eq₁]; ring
    have d0 : (T 0).natDegree≤4 := by
      by_cases e : T 0=0
      · simp [e]
      · have t := d 3
        rw [eq,natDegree_mul (pow_ne_zero _ X_ne_zero) e,natDegree_X_pow] at t
        omega
    refine ⟨T 0,d0,fun i nt ng wn=>mul_right_cancel₀ wn ?_⟩
    have e := deleteTerminal_eq_at_ne (S.decomposition 0) i nt
    change v i*w i=(S.poly 0).eval (c i)+S.tail 0 i at e
    simpa only [z,eval_zero,zero_add,rep _ i ng] using e

end Order15K1Head
end
end RKCert.Paired
