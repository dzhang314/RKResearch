module

public import RKCert.OrderTwelveBand

@[expose] public section
namespace RKCert.Paired.OrderTwelve
open RKCert.Paired RKCert.OneEscape RKCert.Paired.Clock Module
variable {K : Type*} [Field K] [CharZero K]
variable {A : Fin (s+1)→Fin (s+1)→K} {b : Vec K (s+1)} {i : Fin (s+1)}

structure HeadData (A : Fin (s+1)→Fin (s+1)→K)
    (r:ℕ) (U:Submodule K (Vec K (s+1))) (w:Vec K (s+1)) : Prop where
  pos : 2≤r
  inv : U.map (diag (nodes A))≤U
  low : U≤zeroSpace A 5
  rank : finrank K U+r=5
  normalized : ∀ x, fiber (nodes A) x w∈U→fiber (nodes A) x w=0
  f5 : zeroSpace A 5=chain (diag (nodes A)) U w r
  f6 : zeroSpace A 6=chain (diag (nodes A)) U w (r+1)
  f7tail : escape7 A=chain (diag (nodes A)) U w (r+2)
  e7 : treeSpace A 7=pBand A ⊔ chain (diag (nodes A)) U w (r+2)

theorem e7_rank (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 12) (hs:Saturation A b)
    (hi:b i≠0) (hl:∀ j,i<j→b j=0) : finrank K (treeSpace A 7)=14 := by
  rw [e7_exact ha ho hs hi hl,band_rank_add,escape7_rank ha ho hs hi hl]
  intro a h
  exact last_zero_separation ha ho (active_last_normal ha hs hi hl) a (escape7_le_end ha ho hs hi hl h)

theorem exists_head_data (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 12) (hs:Saturation A b)
    (hi:b i≠0) (hl:∀ j,i<j→b j=0) :
    ∃ r U w, HeadData A r U w := by
  have hnon:=f5_noninvariant ha ho hs
  have hstep : finrank K (zeroSpace A 6)≤finrank K (zeroSpace A 5)+1 := by rw [hs.f5,hs.f6]
  obtain ⟨r,U,w,hr,hu,hUF,_,h5,_,_,hd,hN,_⟩ :=
    ordinary_normal_head A 5 hstep hnon
  have hg := RKCert.Endpoint.forward_invariant_hermite_rank ha ho (j:=5) (by decide) U hUF
    (fun v hv=>hu (Submodule.mem_map_of_mem hv))
  change finrank K U+3≤finrank K (zeroSpace A 6) at hg
  rw [hs.f6] at hg
  rw [hs.f5] at hd
  have h6 : zeroSpace A 6=chain (diag (nodes A)) U w (r+1) := by
    rw [ordinary_step hstep hnon,h5,chain_sup_map hu hr]
  have h7 : escape7 A=chain (diag (nodes A)) U w (r+2) := by
    unfold escape7
    rw [h6,chain_sup_map hu (by omega)]
  exact ⟨r,U,w,by omega,hu,hUF,hd.symm,hN,h5,h6,h7,(e7_exact ha ho hs hi hl).trans (by rw [h7])⟩

omit [CharZero K] in
theorem stage_band_step {r:ℕ} {U:Submodule K (Vec K (s+1))} {w : Vec K (s+1)}
    (hh : HeadData A r U w) {j l:ℕ} (hj:7≤j) (hl:0<l)
    (he:treeSpace A j=pBand A ⊔ chain (diag (nodes A)) U w l) :
    treeSpace A j ⊔ (treeSpace A j).map (diag (nodes A)) =
      pBand A ⊔ chain (diag (nodes A)) U w (l+1) := by
  let C := diag (nodes A)
  let P := pBand A
  let Z := chain C U w l
  have hP : P.map C≤treeSpace A j := by
    apply Submodule.map_le_iff_le_comap.mpr
    intro v hv
    exact treeSpace_mono A hj (diag_treeSpace A 6 (pBand_le A le_rfl hv))
  change treeSpace A j=P ⊔ Z at he
  rw [he] at hP
  rw [he,Submodule.map_sup,←chain_sup_map hh.inv hl]
  apply le_antisymm
  · apply sup_le
    · exact sup_le le_sup_left (le_sup_left.trans le_sup_right)
    · exact sup_le (hP.trans (sup_le le_sup_left (le_sup_left.trans le_sup_right)))
        (le_sup_right.trans le_sup_right)
  · apply sup_le
    · exact le_sup_left.trans le_sup_left
    · exact sup_le (le_sup_right.trans le_sup_left) (le_sup_right.trans le_sup_right)

omit [CharZero K] in
theorem tree_chronological_step {r:ℕ} {U:Submodule K (Vec K (s+1))} {w : Vec K (s+1)}
    (hs:Saturation A b) (hh:HeadData A r U w) {j l:ℕ} (hj:7≤j) (hj9:j≤9) (hl:0<l)
    (he:treeSpace A j=pBand A ⊔ chain (diag (nodes A)) U w l)
    (hr:finrank K (treeSpace A j)=j+7)
    (hna:¬(treeSpace A j).map (diag (nodes A))≤treeSpace A j) :
    treeSpace A (j+1)=pBand A ⊔ chain (diag (nodes A)) U w (l+1) ∧
      finrank K (treeSpace A (j+1))=(j+1)+7 := by
  let V := treeSpace A j ⊔ (treeSpace A j).map (diag (nodes A))
  have hlt : treeSpace A j < V := lt_of_le_of_ne le_sup_left
    (fun e => hna (le_sup_right.trans (le_of_eq e.symm)))
  have hV : V≤treeSpace A (j+1) := sup_le (treeSpace_mono A (by omega))
    (Submodule.map_le_iff_le_comap.mpr (diag_treeSpace A j))
  have hvl := Submodule.finrank_lt_finrank_of_lt hlt
  have hvu := Submodule.finrank_mono hV
  have hc := hs.caps (j+1) (by omega)
  have e : V=treeSpace A (j+1) := Submodule.eq_of_le_of_finrank_le hV (by omega)
  exact ⟨e.symm.trans (stage_band_step hh hj hl he),by omega⟩

theorem stage_charts {r:ℕ} {U:Submodule K (Vec K (s+1))} {w : Vec K (s+1)}
    (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b 12) (hs:Saturation A b)
    (hi:b i≠0) (hl:∀ j,i<j→b j=0)
    (hh:HeadData A r U w)
    (hna:∀j,7≤j→j≤9→¬(treeSpace A j).map (diag (nodes A))≤treeSpace A j) :
    ∀ k≤3, treeSpace A (7+k)=pBand A ⊔ chain (diag (nodes A)) U w (r+2+k) ∧
      finrank K (treeSpace A (7+k))=14+k := by
  intro k hk
  induction k with
  | zero => exact ⟨hh.e7,e7_rank ha ho hs hi hl⟩
  | succ k ih =>
    obtain ⟨he,hr⟩:=ih (by omega)
    have hr' : finrank K (treeSpace A (7+k))=7+k+7 := by omega
    obtain ⟨he',hr''⟩:=tree_chronological_step hs hh (j:=7+k) (l:=r+2+k) (by omega) (by omega)
      (by omega) he hr' (hna (7+k) (by omega) (by omega))
    have eqn : 7+(k+1)=7+k+1 := by omega
    rw [eqn]
    exact ⟨he',by omega⟩

omit [CharZero K] in
/-- Full exposure of the length-r head: each of the final four clock
extensions is paid for once, so at least r+5 distinct effective sites exist. -/
theorem chart_top_and_sites {r:ℕ} {U:Submodule K (Vec K (s+1))} {w : Vec K (s+1)}
    (hs:Saturation A b)
    (e9:treeSpace A 9=pBand A ⊔ chain (diag (nodes A)) U w (r+4))
    (e10:treeSpace A 10=pBand A ⊔ chain (diag (nodes A)) U w (r+5))
    (hr9:finrank K (treeSpace A 9)=16) (hr10:finrank K (treeSpace A 10)=17) :
    treeSpace A 10=⊤ ∧ r+5≤(headSites (nodes A) w).card := by
  have ht : treeSpace A 10=⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [hr10,show finrank K (Vec K (s+1))=s+1 by simp [Vec],hs.size]
  have hp := (chain_le_iff (T:=diag (nodes A)) (U:=U) (w:=w) (r+4)).mp le_rfl
  have hin (k:ℕ) (hk:k<r+4) : (diag (nodes A)^k) w∈treeSpace A 9 :=
    (show chain (diag (nodes A)) U w (r+4)≤treeSpace A 9 from e9 ▸ le_sup_right) (hp.2 k hk)
  have hn : (diag (nodes A)^(r+4)) w∉treeSpace A 9 := by
    intro h
    have chle : chain (diag (nodes A)) U w (r+5)≤treeSpace A 9 := by
      apply (chain_le_iff _).mpr
      refine ⟨(show chain (diag (nodes A)) U w (r+4) ≤ treeSpace A 9 from e9 ▸ le_sup_right).trans' hp.1,?_⟩
      intro k hk
      by_cases hb:k<r+4
      · exact hin k hb
      · have e:k=r+4 := by omega
        exact e ▸ h
    have he : treeSpace A 10≤treeSpace A 9 := by rw [e10];exact sup_le (pBand_le _ (by decide)) chle
    have hdim:=Submodule.finrank_mono he
    omega
  have hs := more_sites_than_paid hin hn
  exact ⟨ht,by omega⟩

end RKCert.Paired.OrderTwelve

