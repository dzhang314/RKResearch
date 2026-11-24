module

public import RKCert.DirkUnitBand
public import RKCert.CoreSupport

@[expose] public section

/-! # The two exhaustive heads in a putative grade-six unit band

The native rank gains leave either an invariant grade-three mask algebra or
a grade-three head whose amplitude is polynomial on its own physical support.
These are structural necessary conditions only. -/

namespace RKCert.Paired.Clock
open RKCert.OneEscape Module Polynomial
variable {K : Type*} [Field K] {s : ℕ}
variable {A : Fin s → Fin s → K}
variable {c w : Vec K s} {U : Submodule K (Vec K s)}

theorem not_paid_of_noninvariant {n : ℕ} (hU : U.map (diag c)≤U) (hn : 0<n)
    (h : ¬ (chain (diag c) U w n).map (diag c)≤chain (diag c) U w n) :
    (diag c^n) w∉chain (diag c) U w n := by
  intro hm
  apply h
  apply (le_sup_right : _ ≤ chain (diag c) U w n ⊔ _).trans
  rw [chain_sup_map hU hn,chain]
  exact sup_le le_rfl ((Submodule.span_singleton_le_iff_mem _ _).mpr hm)

theorem head_sites_of_noninvariant {n : ℕ} (hU : U.map (diag c)≤U) (hn : 0<n)
    (h : ¬ (chain (diag c) U w n).map (diag c)≤chain (diag c) U w n) :
    n<(headSites c w).card :=
  more_sites_than_paid ((chain_le_iff n).mp le_rfl).2 (not_paid_of_noninvariant hU hn h)

variable [CharZero K] {p : ℕ} {b : Vec K s}

theorem dirk_six_head_starts_at_four (ha : ∀ i j : Fin s, i.val<j.val → A i j=0)
    (ho : HasTreeOrderAtLeast A b p) (hp : 8≤p)
    (bad : ¬ finrank K (zeroSpace A 3)+4≤finrank K (zeroSpace A 6))
    (inv : (zeroSpace A 3).map (diag (nodes A))≤zeroSpace A 3) :
    ∃ w : Vec K s, MulClosed (zeroSpace A 3) ∧ 3<(headSites (nodes A) w).card ∧
      (∀ k ≤ 2, zeroSpace A (4+k)=chain (diag (nodes A)) (zeroSpace A 3) w (1+k)) := by
  obtain ⟨hUnit,hNon⟩ := dirk_unit_band_of_no_grade_six_surplus ha ho hp bad
  have h4 : finrank K (zeroSpace A 5)≤finrank K (zeroSpace A 4)+1 :=
    (hUnit 4 (by decide) (by decide)).le
  obtain ⟨r,U,w,pos,hU,hUF,hmax,hF,_,_,hDim,normal,_⟩ :=
    ordinary_normal_head A 4 h4 (hNon 4 (by decide) (by decide))
  have hF3 : zeroSpace A 3≤U := hmax _ inv (zeroSpace_mono A (by decide))
  have hh := Submodule.finrank_mono hF3
  have h34 : finrank K (zeroSpace A 4)=finrank K (zeroSpace A 3)+1 :=
    hUnit 3 (by decide) (by decide)
  have hr : r=1 := by omega
  have eqU : zeroSpace A 3=U := Submodule.eq_of_le_of_finrank_eq hF3 (by omega)
  subst r
  subst U
  have hBand := ordinary_staircase (h:=2) hU (by decide) hF
    (fun k hk => (hUnit (4+k) (by omega) (by omega)).le)
    (fun k hk => hNon (4+k) (by omega) (by omega))
  have eq6 : zeroSpace A 6=chain (diag (nodes A)) (zeroSpace A 3) w 3 := hBand 2 (by decide)
  have hn := hNon 6 (by decide) (by decide)
  rw [eq6] at hn
  have hs := head_sites_of_noninvariant inv (by decide) hn
  refine ⟨w,?_,hs,hBand⟩
  intro u hu v hv
  exact core_mul (j:=3) (k:=3) inv le_rfl normal hs (le_of_eq eq6) hu hv

theorem dirk_six_head_starts_at_three (ha : ∀ i j : Fin s, i.val<j.val → A i j=0)
    (ho : HasTreeOrderAtLeast A b p) (hp : 8≤p)
    (bad : ¬ finrank K (zeroSpace A 3)+4≤finrank K (zeroSpace A 6))
    (inv : ¬ (zeroSpace A 3).map (diag (nodes A))≤zeroSpace A 3) :
    ∃ (r : ℕ) (U : Submodule K (Vec K s)) (w : Vec K s) (P : K[X]),
      0<r ∧ U.map (diag (nodes A))≤U ∧ U≤zeroSpace A 3 ∧ MulClosed U ∧
      (∀ i, Live U i → w i=0) ∧ r+3<(headSites (nodes A) w).card ∧
      (∀ k≤3,zeroSpace A (3+k)=chain (diag (nodes A)) U w (r+k)) ∧
      P≠0 ∧ P.natDegree+r≤4 ∧ (∀ i, w i≠0 → w i=P.eval (nodes A i)) := by
  classical
  obtain ⟨hUnit,hNon⟩ := dirk_unit_band_of_no_grade_six_surplus ha ho hp bad
  have h3 : finrank K (zeroSpace A 4)≤finrank K (zeroSpace A 3)+1 :=
    (hUnit 3 (by decide) (by decide)).le
  obtain ⟨r,U,w,pos,hU,hUF,_,hF,paid,_,_,normal,_⟩ :=
    ordinary_normal_head A 3 h3 inv
  have hBand := ordinary_staircase (h:=3) hU pos hF
    (fun k hk => (hUnit (3+k) (by omega) (by omega)).le) (fun k hk => by
      by_cases e : k=0
      · simpa [e] using inv
      · exact hNon (3+k) (by omega) (by omega))
  have eq6 : zeroSpace A 6=chain (diag (nodes A)) U w (r+3) := hBand 3 (by decide)
  have out := hNon 6 (by decide) (by decide)
  rw [eq6] at out
  have hsites := head_sites_of_noninvariant hU (by omega) out
  have hm (u) (hu : u∈U) (v) (hv : v∈zeroSpace A 3) : u*v∈U :=
    core_mul (j:=3) (k:=3) hU hUF normal hsites (le_of_eq eq6) hu hv
  have hmul : MulClosed U := fun u hu v hv => hm u hu v (hUF hv)
  have hwF : w∈zeroSpace A 3 := by simpa using paid 0 pos
  obtain ⟨v,_,hD,hEq⟩ := disjoint_head hU hmul (fun u hu => hm u hu w hwF)
  have band (k : ℕ) (hk : k≤3) : zeroSpace A (3+k)=chain (diag (nodes A)) U v (r+k) :=
    (hBand k hk).trans (hEq _).symm
  have eq6' : zeroSpace A 6=chain (diag (nodes A)) U v (r+3) := band 3 (by decide)
  have hout' := hNon 6 (by decide) (by decide)
  rw [eq6'] at hout'
  have sites' := head_sites_of_noninvariant hU (by omega) hout'
  have powers (k : ℕ) (hk : k≤2*r-2) :
      (diag (nodes A)^k) (v*v)∈chain (diag (nodes A)) U v (r+3) := by
    let x := min k (r-1)
    let y := k-x
    have hx : x<r := by
      exact (Nat.min_le_right k (r-1)).trans_lt (by omega)
    have hy : y<r := by
      dsimp [y,x]
      omega
    have hk' : x+y=k := by
      dsimp [x,y]
      exact Nat.add_sub_of_le (Nat.min_le_left _ _)
    have h3' : zeroSpace A 3=chain (diag (nodes A)) U v r := by simpa using band 0 (by decide)
    have hmem (l : ℕ) (hl : l<r) : (diag (nodes A)^l) v∈zeroSpace A 3 :=
      h3'.symm ▸ ((chain_le_iff r).mp le_rfl).2 l hl
    rw [←eq6']
    have prod := zeroSpace_mul (hmem x hx) (hmem y hy)
    have he : (diag (nodes A)^k) (v*v) =
        (diag (nodes A)^x) v * (diag (nodes A)^y) v := by
      ext i
      simp only [pow_diag_apply,Pi.mul_apply]
      rw [←hk',pow_add]
      ring
    rw [he]
    exact prod
  obtain ⟨P,hp',values⟩ := multiplier_degree hD sites' powers
  have hn : P≠0 := by
    intro hP
    have hn : (headSites (nodes A) v).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨z,hz⟩ := hn
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
    have hvi := (Finset.mem_filter.mp hi).2
    exact hvi (by simpa [hP] using values i hvi)
  have deg := hp'.resolve_left hn
  exact ⟨r,U,v,P,pos,hU,hUF,hmul,hD,sites',band,hn,by omega,values⟩

end RKCert.Paired.Clock
