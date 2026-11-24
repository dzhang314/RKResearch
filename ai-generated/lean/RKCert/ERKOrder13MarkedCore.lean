module
public import RKCert.ERKOrder13MarkedLeakage
public import RKCert.ERKFiniteCore
public import RKCert.ERKFiniteKnots
public import RKCert.OrderTwelveCoreRanks
public import RKCert.ERKOrder13PrefixReverse

@[expose] public section

/-! # Low physical grades in the marked prefix
The terminal line is an actual part of the invariant core. Graded products
are kept in the augmented defect spaces and localized before the proven
three-shift elimination is used; no actual F-grade is confused with a
rank-only horizon.
-/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Paired.Clock RKCert.OneEscape Module Polynomial
variable {K:Type*} [Field K] {s a r:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
variable {U:Submodule K (Vec K (s+1))} {w:Vec K (s+1)} {G:K[X]}
set_option maxHeartbeats 2800000

theorem marked13_defect_rank (ho:HasTreeOrderAtLeast A b 13) (M:Margin A b 6 1 1)
    (S:Saturated A b 6 1) (j:ℕ) (hj:j≤12) :
    finrank K (defectPlus A 1 j)=finrank K (zeroSpace A j)+1 := by
  unfold defectPlus
  exact add_tail_rank M (by decide) (disjoint_tail_of_order ho S.lastLive
    (V:=zeroSpace A j) le_rfl (by omega))

theorem marked13_core_exact (ho:HasTreeOrderAtLeast A b 13)
    (S:Saturated A b 6 1) (M:Margin A b 6 1 1) (H:MarkedHead A 6 1 r U w)
    (j:ℕ) (hj:j≤r) :
    core (diag (nodes A)) (defectPlus A 1 5) j=chain (diag (nodes A)) U w (r-j) := by
  let D:=diag (nodes A)
  let F:=defectPlus A 1 5
  have f5 : F=chain D U w r := H.paid 5 le_rfl (by decide)
  have f6 : defectPlus A 1 6=chain D U w (r+1) := H.paid 6 (by decide) le_rfl
  have paid (k:ℕ) (hk:k<r) : (D^k) w∈F := by
    rw [f5]
    exact ((chain_le_iff r).mp le_rfl).2 k hk
  have out : (D^r) w∉F := by
    intro h
    have e :defectPlus A 1 6≤F := by
      rw [f6,chain]
      exact sup_le (le_of_eq f5.symm) ((Submodule.span_singleton_le_iff_mem ..).mpr h)
    have dim:=Submodule.finrank_mono e
    change finrank K (defectPlus A 1 6)≤finrank K (defectPlus A 1 5) at dim
    rw [marked13_defect_rank ho M S 6 (by decide),marked13_defect_rank ho M S 5 (by decide),
      S.fRank 6 (by decide) le_rfl,S.fRank 5 le_rfl (by decide)] at dim
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
    refine ⟨invariant_le_core H.core H.stable j,?_⟩
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

theorem marked13_lower_into_core (ho:HasTreeOrderAtLeast A b 13)
    (S:Saturated A b 6 1) (M:Margin A b 6 1 1) (H:MarkedHead A 6 1 r U w)
    {k:ℕ} (hk:k≤5) (hr:5-k≤r) :
    defectPlus A 1 k≤chain (diag (nodes A)) U w (r-(5-k)) := by
  rw [←marked13_core_exact ho S M H _ hr]
  intro v hv
  apply mem_core.mpr
  intro j hj
  exact Fplus_mono A 1 (by omega) (Fplus_power hv j)

theorem marked13_four_exact (ho:HasTreeOrderAtLeast A b 13)
    (S:Saturated A b 6 1) (M:Margin A b 6 1 1) (H:MarkedHead A 6 1 r U w)
    (h4:finrank K (zeroSpace A 4)=4) :
    defectPlus A 1 4=chain (diag (nodes A)) U w (r-1) := by
  have r2:=H.rTwo
  have incl:=marked13_lower_into_core ho S M H (k:=4) (by decide) (by omega)
  apply Submodule.eq_of_le_of_finrank_le incl
  change finrank K (chain (diag (nodes A)) U w (r-1))≤finrank K (defectPlus A 1 4)
  rw [marked13_defect_rank ho M S 4 (by decide),h4]
  have cap:=RKCert.Paired.OrderTwelve.chain_rank_cap (A:=A) (U:=U) (w:=w) (r-1)
  have rank:=H.rank
  omega

theorem marked13_local_core_product [CharZero K] (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13)
    (S:Saturated A b 6 1) (M:Margin A b 6 1 1) (C:Chart13 A 1 a r U w G)
    {j k:ℕ} (corej:U≤defectPlus A 1 j) (budget:j+k≤8)
    {u v:Vec K (s+1)} (hu:u∈U) (hv:v∈defectPlus A 1 k) : u*v∈U := by
  classical
  let c:=nodes A
  let D:=diag c
  let F:=defectPlus A 1 8
  have dec : u*v=∑ z∈sites c, fiber c z u*v := by rw [←Finset.sum_mul,sum_fibers]
  rw [dec]
  apply U.sum_mem
  intro z _
  let h:=fiber c z u*v
  have fu : fiber c z u∈U := fiber_mem C.marked.stable z hu
  have f0:h∈F := Fplus_mono A 1 budget (Fplus_mul (corej fu) hv)
  have scale : D h=z • h := by
    ext i
    by_cases e:c i=z
    · simp [D,h,fiber,e]
    · simp [D,h,fiber,e]
  have f1:D h∈F := by rw [scale];exact F.smul_mem _ f0
  have f2:D (D h)∈F := by rw [scale,map_smul];exact F.smul_mem _ f1
  have hb := (order13_marked_no_leak ha ho S M C f0 f1 f2).1
  have count : headLen 6 a r 8<(headSites c w).card := by
    have h:=band13_sites C
    change headLen 6 a r 10≤(headSites c w).card at h
    have w:=C.width
    unfold headLen at *
    omega
  apply localized_mem (z:=z) C.marked.stable C.marked.norm count hb
  intro i hzi
  change c i≠z at hzi
  simp [h,fiber,hzi]

theorem marked13_clean_head (C:Chart13 A 1 a r U w G) (mulc:MulClosed U)
    (hp:∀ u∈U,u*w∈U) :
    ∃ v:Vec K (s+1),Chart13 A 1 a r U v G ∧∀ i,Live U i→v i=0 := by
  obtain ⟨v,_,dis,e⟩:=disjoint_head C.marked.stable mulc hp
  have norm (z:K) (hz:fiber (nodes A) z v∈U) : fiber (nodes A) z v=0 := by
    classical
    ext i
    change fiber (nodes A) z v i=0
    by_contra hn
    have x:=dis i ⟨_,hz,hn⟩
    simp [fiber,x] at hn
  have H : MarkedHead A 6 1 r U v :=
    ⟨C.marked.rTwo,C.marked.rank,C.marked.core,C.marked.stable,norm,
      fun j hj hq=> (C.marked.paid j hj hq).trans (e _).symm,
      C.marked.edge.trans (e _).symm,C.marked.edgeRank⟩
  refine ⟨v,⟨H,C.shape,C.mesh,C.meshDegree,C.meshPaid,?_,C.rich⟩,dis⟩
  intro j hj hm
  unfold Band13 forwardBand
  rw [e]
  exact C.chart j hj hm

theorem marked13_four_clean [CharZero K] (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 13)
    (S:Saturated A b 6 1) (M:Margin A b 6 1 1) (C:Chart13 A 1 a r U w G)
    (h4:finrank K (zeroSpace A 4)=4) :
    ∃ v:Vec K (s+1),Chart13 A 1 a r U v G ∧MulClosed U∧∀ i,Live U i→v i=0 := by
  have f4:=marked13_four_exact ho S M C.marked h4
  have core4:U≤defectPlus A 1 4 := by rw [f4];exact ((chain_le_iff _).mp le_rfl).1
  have H {u v:Vec K (s+1)} (hu:u∈U) (hv:v∈defectPlus A 1 4) : u*v∈U :=
    marked13_local_core_product ha ho S M C (j:=4) (k:=4) core4 (by decide) hu hv
  have mulc:MulClosed U:=fun _ hu _ hv=>H hu (core4 hv)
  have hw:w∈defectPlus A 1 4 := by
    rw [f4]
    simpa only [pow_zero,one_apply_eq_self] using
      ((chain_le_iff _).mp le_rfl).2 0 (show 0<r-1 by have := C.marked.rTwo;omega)
  obtain ⟨v,C,dis⟩:=marked13_clean_head C mulc (fun _ hu=>H hu hw)
  exact ⟨v,C,mulc,dis⟩

end RKCert.Paired.FiniteMidpoint
