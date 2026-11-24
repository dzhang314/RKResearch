module

public import RKCert.Dirk15DeletedLocalizedPure
public import RKCert.Dirk15MinimalMovingQuartic

@[expose] public section

/-! # The actual visible two-core branch is invariant under its quartic

Pure localized products are brought back from the numerical deletion
through the true output weight at the original terminal. This does not
infer an integration order on any projected array.
-/
namespace RKCert.Paired
open Module Polynomial RKCert.OneEscape RKCert.Endpoint
open scoped Classical
noncomputable section
variable {K : Type*} [Field K]

section Normalize
variable {n : ℕ} {C : Vec K n→ₗ[K]Vec K n} {U : Submodule K (Vec K n)} {v : Vec K n}

theorem chain_scale_nonzero (a : K) (an : a≠0) (m : ℕ) :
    chain C U (a • v) m=chain C U v m := by
  apply le_antisymm
  · apply (chain_le_iff _).mpr
    have q := (chain_le_iff (T:=C) (U:=U) (w:=v) m).mp le_rfl
    refine ⟨q.1,fun i hi=>?_⟩
    rw [map_smul]
    exact (chain C U v m).smul_mem _ (q.2 i hi)
  · apply (chain_le_iff _).mpr
    have q := (chain_le_iff (T:=C) (U:=U) (w:=a • v) m).mp le_rfl
    refine ⟨q.1,fun i hi=>?_⟩
    have e := q.2 i hi
    rw [map_smul] at e
    exact ((chain C U (a • v) m).smul_mem_iff_of_isUnit (isUnit_iff_ne_zero.mpr an)).mp e

end Normalize

variable [CharZero K]
variable {A : Fin 20→Fin 20→K} {b : Vec K 20}

structure Order15K2Head (A : Fin 20→Fin 20→K) (b : Vec K 20) (v : Vec K 20) where
  head : Order15MinimalHead A b
  core_two : finrank K head.U=2
  physical : head.w=v
  paid : v∈zeroSpace A 4

theorem order15_k2_head {v : Vec K 20} (h : Order15MinimalHead A b)
    (two : finrank K h.U=2) (hv : v∈zeroSpace A 4) (outside : v∉h.U) :
    Nonempty (Order15K2Head A b v) := by
  obtain ⟨u,hu,S,sn,ds,eq⟩ := h.visible_head_degree hv outside
  have s0 : S.natDegree=0 := by rw [two] at ds; exact Nat.eq_zero_of_le_zero ds
  let a := S.coeff 0
  have sa : S=C a := eq_C_of_natDegree_eq_zero s0
  have an : a≠0 := fun e => sn (by rw [sa,e,map_zero])
  have ew : weightedEval (nodes A) h.w S=a • h.w := by
    rw [sa]
    ext i
    rw [weightedEval_apply,eval_C,Pi.smul_apply,smul_eq_mul]
  have ev : v-u=a • h.w := by rw [eq,ew]; abel
  have e (n : ℕ) : chain (diag (nodes A)) h.U v n=chain (diag (nodes A)) h.U h.w n := by
    have t := chain_sub_head (w:=v) h.maximal.2.1 hu n
    rw [ev,chain_scale_nonzero a an] at t
    exact t.symm
  let J : Order15MinimalHead A b := ⟨h.U,v,h.maximal,h.low,h.high,h.ghosts,h.cubic,
    h.six.trans (e _).symm,h.seven.trans (e _).symm,h.seven_escape⟩
  exact ⟨⟨J,two,rfl,hv⟩⟩

namespace Order15MinimalHead
variable (h : Order15MinimalHead A b)

omit [CharZero K] in
theorem deleted_length_next_unpaid (ho : HasTreeOrderAtLeast A b 15)
    (H : Order15MinimalMarkedChart A b) :
    ((deletedClock A)^h.length) (deleteTerminal K 19 h.w) ∉
      deletedHeadOrbit A h.U h.w h.length := by
  intro t
  rw [←deleteTerminal_diag_pow,deletedHeadOrbit_eq] at t
  obtain ⟨x,hx,eq⟩ := t
  have q := ((chain_le_iff (T:=diag (nodes A)) (U:=h.U) (w:=h.w) (h.length+1)).mp le_rfl).2 _ 
    (Nat.lt_succ_self h.length)
  have a : ((diag (nodes A))^h.length) h.w∈zeroSpace A 8 := h.length_next_pure q
  have b : x∈zeroSpace A 8 := zeroSpace_mono A (by decide : 7≤8) (h.seven.ge hx)
  have e := deleted_pure_same ho H.terminal.weight_ne (by decide) b a eq
  exact h.length_next_unpaid (e ▸ h.seven.ge hx)

set_option maxHeartbeats 2200000 in
theorem localized_paid_product_core (D : h.DeletedPencil) (ha : LowerArray A)
    (ho : HasTreeOrderAtLeast A b 15) (H : Order15MinimalMarkedChart A b)
    {x : Vec K 20} (hx : x∈zeroSpace A 10) (a : K)
    (eigen : diag (nodes A) x=a • x) :
    x∈h.U := by
  let d := deleteTerminal K 19
  let c := d (nodes A)
  let C := diag c
  let L := deletedHeadOrbit A h.U h.w
  let U := h.U.map d
  let w := d h.w
  let v := w-Clock.correction c U w
  let L' := chain C U v
  have inv : U.map C≤U := deletedCore_invariant h.maximal.2.1
  have norm : ∀ z,Clock.fiber c z v∈U→Clock.fiber c z v=0 :=
    fun z hz => Clock.normalized c U w z hz
  have ht : Clock.correction c U w∈U := Clock.correction_mem c U w
  have eqL (n : ℕ) : L' n=L n :=
    chain_sub_head inv ht n
  have vd (i : Fin 19) (hi : c i≠a) : d x i=0 := by
    have t : C (d x)=a • d x := by
      change diag (deleteTerminal K 19 (nodes A)) (d x)=_
      rw [←deleteTerminal_diag,eigen,map_smul]
    have s := congrFun t i
    change c i*d x i=a*d x i at s
    have zz : (c i-a)*d x i=0 := by rw [sub_mul,s,sub_self]
    exact (mul_eq_zero.mp zz).resolve_left (sub_ne_zero.mpr hi)
  have out : (C^h.length) v∉L' h.length := by
    intro inc
    have u := ((chain_le_iff (T:=C) (U:=U) (w:=w) h.length).mp le_rfl).1
      (pow_mem inv ht h.length)
    rw [eqL] at inc
    have e := (L h.length).add_mem inc u
    apply h.deleted_length_next_unpaid ho H
    change (C^h.length) w∈L h.length
    simpa only [v,map_sub,sub_add_cancel] using e
  have basic : h.length<(Clock.headSites c v).card :=
    Clock.more_sites_than_paid ((chain_le_iff (T:=C) (U:=U) (w:=v) h.length).mp le_rfl).2 out
  have dx : d x∈U := by
    by_cases fold : deleteTerminal K 19 (((diag (nodes A))^h.length) h.w)∈deletedTreeSpace A 7
    · have t : d x∈L h.length := D.folded_localized_pure_tail ha ho H fold hx a eigen
      exact Clock.localized_mem inv norm basic ((eqL _).ge t) vd
    · have t : d x∈L (h.length+3) := D.unfolded_localized_pure_tail ha ho H fold hx a eigen
      let P := deletedScalarOrbit A 7
      have e11 : deletedTreeSpace A 11=P⊔L (h.length+4) := by
        rcases h.deleted_growth_dichotomy ha ho H with ⟨f,_⟩|⟨_,g⟩
        · exact (fold f).elim
        · exact g 4 (by decide)
      have d11 := (order15_minimal_deleted_band ha ho H 11 (by decide) (by decide)).2
      rw [e11] at d11
      have rr := Submodule.finrank_sup_add_finrank_inf_eq P (L (h.length+4))
      rw [d11] at rr
      have t8 : finrank K P≤8 := Order15MinimalHead.deleted_scalar_rank_upper 7
      have uB : finrank K U≤finrank K h.U := Submodule.finrank_map_le _ _
      have tq := chain_dim_sites (c:=c) (w:=v) (U:=U) (h.length+4)
      change finrank K (L' (h.length+4))≤finrank K U+(Clock.headSites c v).card at tq
      rw [eqL] at tq
      have len := h.length_sum
      have sites : h.length+3<(Clock.headSites c v).card := by omega
      exact Clock.localized_mem inv norm sites ((eqL _).ge t) vd
  obtain ⟨z,hz,eq⟩ := dx
  have hzj : z∈zeroSpace A 10 := zeroSpace_mono A (by decide : 7≤10) (h.maximal.1 hz)
  have e := deleted_pure_same ho H.terminal.weight_ne (by decide) hzj hx eq
  exact e ▸ hz

end Order15MinimalHead

namespace Order15K2Head
variable {v : Vec K 20} (h : Order15K2Head A b v)

theorem preserves_core (D : h.head.DeletedPencil) (ha : LowerArray A)
    (ho : HasTreeOrderAtLeast A b 15) (H : Order15MinimalMarkedChart A b) :
    h.head.U.map (diag v)≤h.head.U := by
  rintro _ ⟨z,hz,rfl⟩
  let c := nodes A
  let U := h.head.U
  have incl : U≤zeroSpace A 6 := by
    rw [h.head.six]
    exact ((chain_le_iff _).mp le_rfl).1
  have eq : diag v z=∑ a∈Clock.sites c,Clock.fiber c a z*v := by
    rw [←Finset.sum_mul,Clock.sum_fibers]
    ext i
    simp [diag_apply,mul_comm]
  rw [eq]
  apply U.sum_mem
  intro a _
  have zf := Clock.fiber_mem h.head.maximal.2.1 a hz
  have paid := zeroSpace_mul h.paid (incl zf)
  have q : Clock.fiber c a z*v∈zeroSpace A 10 := by simpa only [mul_comm] using paid
  have e : diag c (Clock.fiber c a z*v)=a • (Clock.fiber c a z*v) := by
    ext i
    by_cases w : c i=a
    · simp [Clock.fiber,w,diag_apply]
    · simp [Clock.fiber,w,diag_apply]
  exact h.head.localized_paid_product_core D ha ho H q a e

end Order15K2Head
end
end RKCert.Paired
