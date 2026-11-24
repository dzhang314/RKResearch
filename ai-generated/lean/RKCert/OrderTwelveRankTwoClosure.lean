module
public import RKCert.OrderTwelvePureRankTwo
public import RKCert.OrderTwelveCoreRanks
public import RKCert.OrderTwelveReverseChart
public import RKCert.ERKGradeFive

@[expose] public section
namespace RKCert.Paired.OrderTwelve
open RKCert.Paired RKCert.Paired.Clock RKCert.OneEscape Polynomial Module
variable {K:Type*} [Field K] [CharZero K]
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)} {i:Fin (s+1)}
variable {r:ℕ} {U:Submodule K (Vec K (s+1))} {w:Vec K (s+1)}

/-- The final one-head chart requires E9's genuine clock escape, isolated
from evaluation of either final arithmetic gate. -/
structure FullChart (A:Fin (s+1)→Fin (s+1)→K) (r:ℕ)
    (U : Submodule K (Vec K (s+1))) (w:Vec K (s+1)) : Prop where
  head : HeadData A r U w
  e8 : treeSpace A 8=pBand A ⊔ chain (diag (nodes A)) U w (r+3)
  e9 : treeSpace A 9=pBand A ⊔ chain (diag (nodes A)) U w (r+4)
  e10 : treeSpace A 10=pBand A ⊔ chain (diag (nodes A)) U w (r+5)
  e9r : finrank K (treeSpace A 9)=16
  e10r : finrank K (treeSpace A 10)=17
  full : pBand A ⊔ chain (diag (nodes A)) U w (r+5)=⊤
  sites : r+5≤(headSites (nodes A) w).card

theorem full_chart_of_escape9 (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 12)
    (hs:Saturation A b) (hi:b i≠0) (hl:∀ j,i<j→b j=0)
    (h9:¬(treeSpace A 9).map (diag (nodes A))≤treeSpace A 9) :
    ∃ r U w, FullChart A r U w := by
  obtain ⟨r,U,w,hh⟩:=exists_head_data ha ho hs hi hl
  have hR := reverse_seven_nine ha ho hs
  have esc : ∀j:ℕ,7≤j→j≤9→¬(treeSpace A j).map (diag (nodes A))≤treeSpace A j := by
    intro j h7 h9'
    interval_cases j
    · exact hR.noninvariant7
    · exact hR.noninvariant8
    · exact h9
  have e := stage_charts ha ho hs hi hl hh esc
  have ⟨a,_⟩ := e 1 (by decide)
  have ⟨d,f⟩ := e 2 (by decide)
  have ⟨g,h⟩ := e 3 (by decide)
  have e8 : treeSpace A 8=pBand A ⊔ chain (diag (nodes A)) U w (r+3) := a
  have e9 : treeSpace A 9=pBand A ⊔ chain (diag (nodes A)) U w (r+4) := d
  have e10 : treeSpace A 10=pBand A ⊔ chain (diag (nodes A)) U w (r+5) := g
  obtain ⟨ht,sites⟩ := chart_top_and_sites hs e9 e10 f h
  exact ⟨r,U,w,hh,e8,e9,e10,f,h,e10.symm.trans ht,sites⟩

omit [CharZero K] in
theorem disjoint_full_chart (hs:Saturation A b) (h:FullChart A r U w)
    (hU:MulClosed U) (hm:∀ u∈U,u*w∈U) :
    ∃ z:Vec K (s+1), w-z∈U ∧ (∀ j,Live U j→z j=0) ∧ FullChart A r U z := by
  classical
  obtain ⟨z,hz,hdis,e⟩:=disjoint_head h.head.inv hU hm
  have hn : ∀ a, fiber (nodes A) a z∈U→fiber (nodes A) a z=0 := by
    intro a hv
    ext j
    by_cases hj:Live U j
    · simp [fiber,hdis j hj]
    · by_contra ne
      exact hj ⟨_,hv,ne⟩
  have hh : HeadData A r U z :=
    ⟨h.head.pos,h.head.inv,h.head.low,h.head.rank,hn,
      h.head.f5.trans (e _).symm,h.head.f6.trans (e _).symm,h.head.f7tail.trans (e _).symm,
      h.head.e7.trans (by rw [e _])⟩
  have e8 : treeSpace A 8=pBand A ⊔ chain (diag (nodes A)) U z (r+3) := by rw [e,h.e8]
  have e9 : treeSpace A 9=pBand A ⊔ chain (diag (nodes A)) U z (r+4) := by rw [e,h.e9]
  have e10 : treeSpace A 10=pBand A ⊔ chain (diag (nodes A)) U z (r+5) := by rw [e,h.e10]
  obtain ⟨top,sites⟩ := chart_top_and_sites hs e9 e10 h.e9r h.e10r
  exact ⟨z,hz,hdis,hh,e8,e9,e10,h.e9r,h.e10r,e10.symm.trans top,sites⟩

/-- Both ghost cases of the physical rank-two, rank-four chart are ruled out.
Only the late clock escape (needed for FullChart) remains external. -/
theorem exclude_two_four (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 12)
    (hs:Saturation A b) (hi:b i≠0) (hl:∀ j,i<j→b j=0)
    (h:FullChart A 2 U w) (hr:finrank K (zeroSpace A 4)=4) : False := by
  have h4 := four_grade_exact hs h.head hr
  have pp := (chain_le_iff (T:=diag (nodes A)) (U:=U) (w:=w) 1).mp le_rfl
  have le4 : U≤zeroSpace A 4 := by rw [h4];exact pp.1
  have hw4 : w∈zeroSpace A 4 := by
    rw [h4]
    simpa only [pow_zero,Module.End.one_eq_id,LinearMap.id_apply] using pp.2 0 (by decide)
  have sit : 2+3<(headSites (nodes A) w).card := by have := h.sites;omega
  have mul (u v : Vec K (s+1)) (hu:u∈U) (hv:v∈zeroSpace A 4) : u*v∈U :=
    core_grade8_multiplier ha ho hs hi hl h.head h.e8 h.e9 h.e9r sit le4 (by decide) hu hv
  have mU : MulClosed U := fun u hu v hv => mul u v hu (le4 hv)
  obtain ⟨z,hz,hdis,hzC⟩:=disjoint_full_chart hs h mU (fun u hu=>mul u w hu hw4)
  have z4 : z∈zeroSpace A 4 := by
    have hZ := (zeroSpace A 4).sub_mem hw4 (le4 hz)
    simpa only [sub_sub_cancel] using hZ
  have zi := f5_vanish_at_last_active ha ho hs hi hl (zeroSpace_mono A (by decide:4≤5) z4)
  have sq : z*z∈endZero A 8 i := ⟨zeroSpace_mul (A:=A) (m:=4) (n:=4) z4 z4,by change z i*z i=0;rw [zi,zero_mul]⟩
  have h7t : chain (diag (nodes A)) U z 4≤endZero A 7 i := by
    rw [←hzC.head.f7tail]
    exact escape7_le_end ha ho hs hi hl
  have h8t : chain (diag (nodes A)) U z 5≤endZero A 8 i := by
    have hh:=chain_sup_map (w:=z) hzC.head.inv (n:=4) (by decide)
    rw [←hh]
    exact (sup_le_sup h7t (Submodule.map_mono h7t)).trans (endZero_next 7)
  obtain ⟨a,eq⟩:=ghost8_leak ha ho (active_last_normal ha hs hi hl) hzC.e8 h8t sq
  by_cases h:a=0
  · exact exclude_pure_two ha ho hs hi hl hzC.head mU hdis z4 hzC.sites
      (by simpa only [h,zero_smul,sub_zero] using eq)
  · exact exclude_nonzero_ghost_two ha ho hs hi hl hzC.head mU hdis hzC.full a h eq

theorem saturation_at_most_seventeen (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 12)
    (hs:s+1≤17) : Saturation A b := by
  apply saturation ha ho (grade_five_surplus ha (explicit_separated ha ho (by decide) (by omega))) hs

theorem actual_last_at_most_seventeen (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 12)
    (hs:s+1≤17) : b (Fin.last s)≠0 := by
  apply last_weight_of_five_surplus (fun {n} {a} {bb} hA hO=> ?_) ha ho hs
  exact grade_five_surplus hA (explicit_separated hA hO (by decide) (by
    have h := explicit_order_le_stages hA hO
    omega))

end RKCert.Paired.OrderTwelve

