module
public import RKCert.ERKOrder13FirstLeak
public import RKCert.OrderTwelveCoreRanks
public import RKCert.ERKFiniteCore
public import RKCert.ERKFiniteKnots

@[expose] public section
/-! # Physical one-loss lower core and full-odd grade-four product algebra -/

namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Paired.Clock RKCert.OneEscape Polynomial Module
variable {K:Type*} [Field K] {s r:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
variable {U:Submodule K (Vec K (s+1))} {w:Vec K (s+1)} {G:K[X]}
set_option maxHeartbeats 2200000

theorem full13_core_exact (S:Saturated A b 6 1) (H:MarkedHead A 6 0 r U w)
    (j:ℕ) (hj:j≤r) :
    core (diag (nodes A)) (zeroSpace A 5) j=chain (diag (nodes A)) U w (r-j) := by
  let D:=diag (nodes A)
  let F:=zeroSpace A 5
  have f5 : F=chain D U w r := by
    simpa only [defectPlus,tailPlane,ite_true,sup_bot_eq,Nat.sub_self,Nat.add_zero] using H.paid 5 le_rfl (by decide)
  have f6 : zeroSpace A 6=chain D U w (r+1) := by
    simpa only [defectPlus,tailPlane,ite_true,sup_bot_eq] using H.paid 6 (by decide) le_rfl
  have paid (k:ℕ) (hk:k<r) : (D^k) w∈F := by
    rw [f5]
    exact ((chain_le_iff r).mp le_rfl).2 k hk
  have out : (D^r) w∉F := by
    intro h
    have e :zeroSpace A 6≤F := by
      rw [f6,chain]
      exact sup_le (le_of_eq f5.symm) ((Submodule.span_singleton_le_iff_mem ..).mpr h)
    have dim:=Submodule.finrank_mono e
    change finrank K (zeroSpace A 6)≤finrank K (zeroSpace A 5) at dim
    rw [S.fRank 6 (by decide) le_rfl,S.fRank 5 le_rfl (by decide)] at dim
    omega
  have rank (k:ℕ) (hk:k≤r) : finrank K (core D F k)+k≤finrank K F := by
    induction k with
    | zero => exact (le_rfl : finrank K F≤finrank K F)
    | succ k ih =>
      have dec : core D F (k+1)<core D F k := by
        refine lt_of_le_of_ne (descend D F k) (fun eq=>out ?_)
        have p : (D^(r-1-k)) w∈core D F k := by
          apply mem_core.mpr
          intro l hl
          rw [←mul_apply_eq_comp,←pow_add]
          exact paid _ (by omega)
        have e := mem_core.mp (show (D^(r-1-k)) w∈core D F (k+1) from eq.symm ▸ p) (k+1) le_rfl
        rw [←mul_apply_eq_comp,←pow_add,show k+1+(r-1-k)=r by omega] at e
        exact e
      have d := Submodule.finrank_lt_finrank_of_lt dec
      have u := ih (by omega)
      omega
  have incl : chain D U w (r-j)≤core D F j := by
    apply (chain_le_iff _).mpr
    refine ⟨invariant_le_core (fun _ hu=>tail_zero_iff.mp (H.core hu)) H.stable j,?_⟩
    intro k hk
    apply mem_core.mpr
    intro l hl
    rw [←mul_apply_eq_comp,←pow_add]
    exact paid _ (by omega)
  refine (Submodule.eq_of_le_of_finrank_le incl ?_).symm
  have lo:=RKCert.Paired.OrderTwelve.head_succ_rank_cap (A:=A) (U:=U) (w:=w) j (r-j)
  change finrank K (chain D U w (r-j+j))≤finrank K (chain D U w (r-j))+j at lo
  rw [show r-j+j=r by omega,←f5] at lo
  have :=rank j hj
  omega

theorem full13_lower_into_core (S:Saturated A b 6 1) (H:MarkedHead A 6 0 r U w)
    {k:ℕ} (hk:k≤5) (hr:5-k≤r) :
    zeroSpace A k≤chain (diag (nodes A)) U w (r-(5-k)) := by
  rw [←full13_core_exact S H _ hr]
  intro v hv
  apply mem_core.mpr
  intro j hj
  exact zeroSpace_mono A (by omega) (tail_zero_iff.mp (Fplus_power (tail_zero_iff.mpr hv) j))

theorem full13_four_exact (S:Saturated A b 6 1) (H:MarkedHead A 6 0 r U w)
    (h4:finrank K (zeroSpace A 4)=4) :
    zeroSpace A 4=chain (diag (nodes A)) U w (r-1) := by
  have r2:=H.rTwo
  have incl:=full13_lower_into_core S H (k:=4) (by decide) (by omega)
  apply Submodule.eq_of_le_of_finrank_le incl
  have cap:=RKCert.Paired.OrderTwelve.chain_rank_cap (A:=A) (U:=U) (w:=w) (r-1)
  change finrank K (chain (diag (nodes A)) U w (r-1))≤finrank K (zeroSpace A 4)
  rw [h4]
  have rank:=H.rank
  omega

theorem full13_local_core_product [CharZero K] (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13)
    (S:Saturated A b 6 1) (M:Margin A b 6 1 0) (C:Chart13 A 0 6 r U w G)
    {j k:ℕ} (corej:U≤zeroSpace A j) (budget:j+k≤8)
    {u v:Vec K (s+1)} (hu:u∈U) (hv:v∈zeroSpace A k) :
    u*v∈U := by
  classical
  let c:=nodes A
  let D:=diag c
  have dec : u*v=∑ z∈sites c, fiber c z u*v := by rw [←Finset.sum_mul,sum_fibers]
  rw [dec]
  apply U.sum_mem
  intro z _
  have tstable (y : Vec K (s+1)) (hy:y∈U) : D y∈U := C.marked.stable ⟨y,hy,rfl⟩
  have fu : fiber c z u∈U := fiber_mem C.marked.stable z hu
  have f0 : fiber c z u*v∈zeroSpace A 8 := zeroSpace_mono A budget (zeroSpace_mul (corej fu) hv)
  have f1 : D (fiber c z u*v)∈zeroSpace A 8 := by
    have eq : D (fiber c z u*v)=D (fiber c z u)*v := by ext i;simp [D,mul_assoc]
    rw [eq]
    exact zeroSpace_mono A budget (zeroSpace_mul (corej (tstable _ fu)) hv)
  have h := (order13_full_no_leak ha ho S M C f0 f1).1
  have count : headLen 6 6 r 8 < (headSites c w).card := by
    have :=band13_sites C
    unfold headLen at *
    exact lt_of_lt_of_le (by omega) this
  apply localized_mem (z:=z) C.marked.stable C.marked.norm count h
  intro i hzi
  change c i≠z at hzi
  simp [fiber,hzi]

theorem full13_clean_four_head [CharZero K] (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13)
    (S:Saturated A b 6 1) (M:Margin A b 6 1 0) (C:Chart13 A 0 6 r U w G)
    (h4:finrank K (zeroSpace A 4)=4) :
    ∃ v:Vec K (s+1), Chart13 A 0 6 r U v G ∧ MulClosed U ∧ ∀ i,Live U i→v i=0 := by
  have f4:=full13_four_exact S C.marked h4
  have core4 : U≤zeroSpace A 4 := by rw [f4];exact ((chain_le_iff _).mp le_rfl).1
  have mulc : MulClosed U :=
    fun _ hu _ hv=>full13_local_core_product ha ho S M C (j:=4) (k:=4) core4 (by decide) hu (core4 hv)
  have hw4 : w∈zeroSpace A 4 := by
    rw [f4]
    simpa only [pow_zero,one_apply_eq_self] using
      ((chain_le_iff _).mp le_rfl).2 0 (show 0<r-1 by have := C.marked.rTwo;omega)
  obtain ⟨v,_,dis,eq⟩:=disjoint_head C.marked.stable mulc (fun u hu=>full13_local_core_product ha ho S M C (j:=4) (k:=4) core4 (by decide) hu hw4)
  have norm (z:K) (hz:fiber (nodes A) z v∈U) : fiber (nodes A) z v=0 := by
    classical
    ext i
    change fiber (nodes A) z v i=0
    by_contra hn
    have e:=dis i ⟨_,hz,hn⟩
    simp [fiber,e] at hn
  have H : MarkedHead A 6 0 r U v :=
    ⟨C.marked.rTwo,C.marked.rank,C.marked.core,C.marked.stable,norm,
      fun j hj hq=> (C.marked.paid j hj hq).trans (eq _).symm,
      C.marked.edge.trans (eq _).symm,C.marked.edgeRank⟩
  refine ⟨v,⟨H,C.shape,C.mesh,C.meshDegree,C.meshPaid,?_,C.rich⟩,mulc,dis⟩
  intro j hj hm
  unfold Band13 forwardBand
  rw [eq]
  exact C.chart j hj hm

end RKCert.Paired.FiniteMidpoint
