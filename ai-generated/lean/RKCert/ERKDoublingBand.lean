module
public import RKCert.ERKPhysicalContrasts
public import RKCert.CoreSupport

@[expose] public section
namespace RKCert.Endpoint
open RKCert.Paired RKCert.OneEscape Polynomial Module
open scoped Classical
variable {K : Type*} [Field K] [CharZero K] {s p : ℕ}

omit [CharZero K] in
/-- A noninvariant last grade has strictly more effective knots than the
number of powers paid there, even after replacing the head by a core translate. -/
private theorem sites_of_last_escape {c v : Vec K s} {U F : Submodule K (Vec K s)} {n : ℕ}
    (hn : 0<n) (hU : U.map (diag c)≤U) (he : F=chain (diag c) U v n)
    (hout : ¬ F.map (diag c)≤F) : n<(Clock.headSites c v).card := by
  have paid := ((chain_le_iff (T:=diag c) (U:=U) (w:=v) n).mp he.ge).2
  apply Clock.more_sites_than_paid paid
  intro h
  apply hout
  apply le_sup_right.trans
  rw [he,chain_sup_map hU hn]
  change chain (diag c) U v n ⊔ Submodule.span K {(diag c ^ n) v} ≤ chain (diag c) U v n
  exact sup_le le_rfl ((Submodule.span_singleton_le_iff_mem ..).mpr (he ▸ h))

/-- No entire doubling band of grades j,...,2j can have only unit gains,
over an arbitrary characteristic-zero coefficient field. The input is the
actual rooted-tree tableau, not a purported flag or boundary certificate. -/
theorem no_flat_doubling_band {A : Fin s → Fin s → K} {b : Vec K s}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b p) (j : ℕ) (hj : 5≤j) (hp : 4*j≤p)
    (flat : ∀ a<j, finrank K (zeroSpace A (j+a+1)) ≤ finrank K (zeroSpace A (j+a))+1) : False := by
  classical
  let C := diag (nodes A)
  let F := zeroSpace A
  have zeroStep : finrank K (F (j+1))≤finrank K (F j)+1 := by simpa using flat 0 (by omega)
  have non (a : ℕ) (h : a≤j) : ¬(F (j+a)).map C≤F (j+a) := by
    intro inc
    have hc : ∀v∈F (j+a),diag (nodes A) v∈F (j+a) := fun v hv => inc ⟨v,hv,rfl⟩
    cases a with
    | zero =>
      simp only [Nat.add_zero] at hc
      have gain := forward_invariant_hermite_rank ha ho (j:=j) (by omega) (F j) le_rfl hc
      change finrank K (F j)+(j+1)/2≤finrank K (F (j+1)) at gain
      omega
    | succ a =>
      have gain := forward_invariant_incoming_rank ha ho (j:=j+a) (by omega) hc
      have cap := flat a (by omega)
      omega
  have start : ¬(F j).map C≤F j := by simpa using non 0 (by omega)
  obtain ⟨r,U,w,hr,hU,hUF,_,base,_,_,rank,normalized,_⟩ :=
    Clock.ordinary_normal_head A j zeroStep start
  have hC : ∀v∈U,diag (nodes A) v∈U := fun v hv => hU ⟨_,hv,rfl⟩
  have gain := forward_invariant_hermite_rank ha ho (j:=j) (by omega) U hUF hC
  have r2 : 2≤r := by dsimp [F] at zeroStep; omega
  have stair := Clock.ordinary_staircase hU hr base flat (fun a h => non a h.le)
  have last : F (j+j)=chain C U w (r+j) := stair j le_rfl
  have count := sites_of_last_escape (by omega : 0<r+j) hU last (non j le_rfl)
  have hmulu (a : Vec K s) (ha' : a∈U) (v : Vec K s) (hv : v∈F j) : a*v∈U :=
    Clock.core_mul hU hUF normalized count last.le ha' hv
  have closed : Clock.MulClosed U := fun a ha b hb => hmulu a ha b (hUF hb)
  have wmem : w∈F j := by
    have hh := ((chain_le_iff (T:=C) (U:=U) (w:=w) r).mp base.ge).2 0 hr
    simpa using hh
  obtain ⟨v,hdiff,hdis,ch⟩ := Clock.disjoint_head hU closed (fun a ha => hmulu a ha w wmem)
  have firstV : F j=chain C U v r := base.trans (ch r).symm
  have lastV : F (j+j)=chain C U v (r+j) := last.trans (ch (r+j)).symm
  have sites := sites_of_last_escape (by omega : 0<r+j) hU lastV (non j le_rfl)
  have paid := ((chain_le_iff (T:=C) (U:=U) (w:=v) r).mp firstV.ge).2
  have vmem : v∈F j := by simpa using paid 0 hr
  have vne : ∃ i,v i≠0 := by
    by_contra! hm
    have hz : Clock.headSites (nodes A) v=∅ := by
      unfold Clock.headSites
      simp [hm]
    rw [hz,Finset.card_empty] at sites
    omega
  have mulband (k : ℕ) (hk : k≤(r-1)+(r-1)) : (C^k) (v*v) ∈ chain C U v (r+j) := by
    let i := min k (r-1)
    let l := k-i
    have hi : i<r := by dsimp [i]; omega
    have hl : l<r := by dsimp [i,l]; omega
    have he : i+l=k := by dsimp [i,l]; omega
    have eq : (C^k) (v*v)=(C^i) v * (C^l) v := by
      ext t
      simp only [C,Clock.pow_diag_apply,Pi.mul_apply]
      rw [←he,pow_add]; ring
    rw [eq,←lastV]
    exact zeroSpace_mul (paid _ hi) (paid _ hl)
  obtain ⟨P,hdegree,values⟩ := Clock.multiplier_degree (a:=v) hdis sites mulband
  have hP : P≠0 := by
    obtain ⟨i,hi⟩ := vne
    rintro rfl
    exact hi (by simpa using values i hi)
  have hd := hdegree.resolve_left hP
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j≠0)
  have hs := explicit_order_le_stages ha ho
  have sep : Separated A (2*(m+1)) := explicit_separated ha ho (by omega) (by omega)
  have he : 2*(m+1)=(m+1)+(m+1) := by omega
  refine no_disjoint_polynomial_head_doubling ha ho (by omega : 4≤m) (by omega) sep U hUF hC
    v vmem (he ▸ lastV.le) ?_ P hP (by omega) values
  intro x hx i hi
  by_contra h
  exact hi (hdis i ⟨x,hx,h⟩)

end RKCert.Endpoint
