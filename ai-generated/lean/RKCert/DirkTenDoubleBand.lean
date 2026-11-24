module
public import RKCert.DirkFiveTenSurplus
public import RKCert.DirkOverlappingHead
@[expose] public section
namespace RKCert.Paired.Terminal
open Module Polynomial RKCert.OneEscape
variable {K:Type*} [Field K] [CharZero K] {s p:ℕ} {A:Fin s→Fin s→K} {b:Vec K s}
noncomputable section

/-- The actual early and late ordinary head bands forced by the putative
single rank payment at grade six. All spaces live on the original tableau. -/
structure TenDoubleBand (A:Fin s→Fin s→K) (V U:Submodule K (Vec K s)) (g w:Vec K s) (r n:ℕ) : Prop where
  early_pos:0<r
  late_pos:0<n
  early_invariant:V.map (diag (nodes A))≤V
  late_invariant:U.map (diag (nodes A))≤U
  early_paid:V≤zeroSpace A 4
  late_paid:U≤zeroSpace A 6
  included:V≤U
  early:∀k≤1,zeroSpace A (4+k)=chain (diag (nodes A)) V g (r+k)
  late:∀k≤4,zeroSpace A (6+k)=chain (diag (nodes A)) U w (n+k)
  extra:chain (diag (nodes A)) V g (r+2)≤zeroSpace A 6
  outside:g∉U
  normalized:∀z,Clock.fiber (nodes A) z w∈U→Clock.fiber (nodes A) z w=0
  sites:n+4<(Clock.headSites (nodes A) w).card
  count:finrank K U+n=finrank K V+r+3

omit [CharZero K] in
private theorem count_sites {c v:Vec K s} {U F:Submodule K (Vec K s)} {n:ℕ}
    (pos:0<n) (inv:U.map (diag c)≤U) (eqn:F=chain (diag c) U v n)
    (out:¬F.map (diag c)≤F) : n<(Clock.headSites c v).card := by
  have paid:=((chain_le_iff (T:=diag c) (U:=U) (w:=v) n).mp eqn.ge).2
  apply Clock.more_sites_than_paid paid
  intro hh
  apply out
  apply le_sup_right.trans
  rw [eqn,chain_sup_map inv pos]
  change chain (diag c) U v n ⊔ Submodule.span K {(diag c^n) v}≤chain (diag c) U v n
  exact sup_le le_rfl ((Submodule.span_singleton_le_iff_mem ..).mpr (eqn ▸ hh))

theorem ten_double_band_of_rank (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b p) (hp:15≤p)
    (small:finrank K (zeroSpace A 10)≤finrank K (zeroSpace A 3)+8) :
    ∃V U g w r n, TenDoubleBand A V U g w r n :=by
  let F:=zeroSpace A
  let T:=diag (nodes A)
  have g(a n:ℕ)(aa:2≤a)(ab:a≤n)(endp:n≤10):finrank K (F a)+(n-a)≤finrank K (F n):=
    flag_gain ha ho aa ab (by omega)
  change finrank K (F 10)≤finrank K (F 3)+8 at small
  have six:=dirk_grade_six_surplus ha ho (by omega)
  change finrank K (F 3)+4≤finrank K (F 6) at six
  have five:=grade_five_ten_surplus ha ho hp
  change finrank K (F 5)+6≤finrank K (F 10) at five
  have all(j:ℕ)(lo:6≤j)(hi:j≤10):finrank K (F j)=finrank K (F 3)+(j-2):=by
    have l:=g 6 j (by decide) lo hi
    have r:=g j 10 (by omega) hi (by decide)
    omega
  have a4:finrank K (F 4)=finrank K (F 3)+1:=by have:=g 3 4 (by decide) (by decide) (by decide);have:=g 4 5 (by decide) (by decide) (by decide);omega
  have a5:finrank K (F 5)=finrank K (F 3)+2:=by have:=g 3 5 (by decide) (by decide) (by decide);omega
  have not_out (j:ℕ) (lo:4≤j) (hi:j≤10) (unit:finrank K (F (j+1))≤finrank K (F j)+1) : ¬ (F j).map T≤F j:=by
    intro inv
    have inc:=dirk_forward_invariant_outgoing ha ho (j:=j) (by omega) (F j) le_rfl (fun _ hz=>inv ⟨_,hz,rfl⟩)
    change finrank K (F j)+j/2≤finrank K (F (j+1)) at inc;omega
  have not_in (j:ℕ) (lo:5≤j) (hi:j≤10) (unit:finrank K (F j)≤finrank K (F (j-1))+1) : ¬(F j).map T≤F j:=by
    intro inv
    have inc:=dirk_forward_invariant_incoming ha ho (j:=j) (by omega) (fun _ hz=>inv ⟨_,hz,rfl⟩)
    change finrank K (F (j-1))+(j-1)/2≤finrank K (F j) at inc;omega
  have unit4:finrank K (F (4+1))≤finrank K (F 4)+1:=by change finrank K (F 5)≤_;omega
  have e4:=not_out 4 le_rfl (by decide) unit4
  have e5:=not_in 5 le_rfl (by decide) (by change finrank K (F 5)≤finrank K (F 4)+1;omega)
  have steps(j:ℕ)(lo:6≤j)(hi:j<10):finrank K (F (j+1))≤finrank K (F j)+1:=by rw [all _ (by omega) (by omega),all _ lo (by omega)];omega
  have es(j:ℕ)(lo:6≤j)(hi:j<10):¬(F j).map T≤F j:=not_out j (by omega) (by omega) (steps j lo hi)
  have e10:=not_in 10 (by decide) (by decide) (by change finrank K (F 10)≤finrank K (F 9)+1;exact steps 9 (by decide) (by decide))
  obtain ⟨r,V,g,hr,vI,vF,_,early,_,_,rc,_,_⟩:=Clock.ordinary_normal_head A 4 unit4 e4
  obtain ⟨n,U,w,hn,uI,uF,maximal,late,_,_,nc,normal,_⟩:=Clock.ordinary_normal_head A 6 (steps 6 le_rfl (by decide)) (es 6 le_rfl (by decide))
  have subset:V≤U:=maximal V vI (vF.trans (zeroSpace_mono A (by decide)))
  have eb(k:ℕ)(hk:k≤1):F (4+k)=chain T V g (r+k):=by
    apply Clock.ordinary_staircase (h:=1) vI hr early _ _ k hk
    · intro a aa
      obtain rfl:a=0:=by omega
      exact unit4
    · intro a aa
      obtain rfl:a=0:=by omega
      exact e4
  have lb(k:ℕ)(hk:k≤4):F (6+k)=chain T U w (n+k):=
    Clock.ordinary_staircase (h:=4) uI hn late (fun a aa=>steps _ (by omega) (by omega))
      (fun a aa=>es _ (by omega) (by omega)) k hk
  have p2:chain T V g (r+2)≤F 6:=by
    rw [show r+2=(r+1)+1 by omega,←chain_sup_map vI (by omega),←eb 1 le_rfl]
    exact sup_le (zeroSpace_mono A (by decide)) (Submodule.map_le_iff_le_comap.mpr (diag_zeroSpace A 5))
  have go:g∉U:=by
    intro inside
    have allU:chain T V g (r+2)≤U:=(chain_le_iff _).mpr ⟨subset,fun k _=>pow_mem uI inside k⟩
    have lt:F 5<F 5 ⊔ (F 5).map T:=lt_of_le_of_ne le_sup_left (fun e=>e5 (le_sup_right.trans (le_of_eq e.symm)))
    have both:F 5 ⊔ (F 5).map T=chain T V g (r+2):=by rw [eb 1 le_rfl,chain_sup_map vI (by omega)]
    have dim:finrank K (F 5)<finrank K U:=by rw [both] at lt;exact (Submodule.finrank_lt_finrank_of_lt lt).trans_le (Submodule.finrank_mono allU)
    have quota:=dirk_forward_invariant_outgoing ha ho (j:=6) (by omega) U uF (fun _ hz=>uI ⟨_,hz,rfl⟩)
    change finrank K U+3≤finrank K (F 7) at quota
    have:=all 7 (by decide) (by decide);omega
  refine ⟨V,U,g,w,r,n,⟨hr,hn,vI,uI,vF,uF,subset,eb,lb,p2,go,normal,?_,?_⟩⟩
  · exact count_sites (by omega) uI (lb 4 le_rfl) e10
  · change finrank K (F 4)=finrank K V+r at rc
    change finrank K (F 6)=finrank K U+n at nc
    have:=all 6 le_rfl (by decide);omega

namespace TenDoubleBand
omit [CharZero K] in
theorem narrow (h:TenDoubleBand A V U g w r n) :
    ∃u∈U,∃L:K[X], L≠0 ∧ L.natDegree+(finrank K U-finrank K V)≤1 ∧
      ∀i,g i=u i+L.eval (nodes A i)*w i :=by
  have paid(k:ℕ)(hk:k≤r+1):(diag (nodes A)^k) g∈chain (diag (nodes A)) U w n:=by
    have step:=((chain_le_iff (T:=diag (nodes A)) (U:=V) (w:=g) (r+2)).mp h.extra).2 k (by omega)
    simpa only [Nat.add_zero] using (h.late 0 (by decide) ▸ step)
  have sites:=h.sites
  obtain ⟨u,hu,L,de,eqn⟩:=Clock.overlapping_head_degree h.late_invariant h.normalized (by omega) paid
  have nz:L≠0:=by
    intro z
    apply h.outside
    have e:g=u:=by ext i;simpa [z] using eqn i
    exact e ▸ hu
  refine ⟨u,hu,L,nz,?_,eqn⟩
  have d:=de.resolve_left nz
  have dim:=Submodule.finrank_mono h.included
  have count:=h.count
  omega
end TenDoubleBand
end
end RKCert.Paired.Terminal

