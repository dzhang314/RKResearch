module
public import RKCert.Dirk14QuarticRank
public import RKCert.DirkEvenJointSupport
@[expose] public section
namespace RKCert.Paired.Terminal
open Module RKCert.OneEscape
variable {K : Type*} [Field K] [CharZero K] {s m : ℕ}
variable {A : Fin (s+1) → Fin (s+1) → K} {b : Vec K (s+1)}
noncomputable section

/-- One and the same normalized head and maximal invariant core across all
ordinary defect grades from five through the midpoint. -/
structure MidpointHead (A : Fin (s+1)→Fin (s+1)→K) (m : ℕ)
    (U : Submodule K (Vec K (s+1))) (w : Vec K (s+1)) (r : ℕ) : Prop where
  positive : 0<r
  invariant : U.map (diag (nodes A))≤U
  paid : U≤zeroSpace A 5
  largest : ∀ W : Submodule K (Vec K (s+1)), W≤zeroSpace A m → W.map (diag (nodes A))≤W → W≤U
  lower : 2≤finrank K U
  upper : finrank K U≤3
  count : finrank K U+r=4
  normalized : ∀ a, Clock.fiber (nodes A) a w∈U → Clock.fiber (nodes A) a w=0
  band : ∀ j, 5≤j → j≤m → zeroSpace A j=chain (diag (nodes A)) U w (r+(j-5))

theorem midpoint_head_of_quartic_hidden (hm : 7≤m) (ha : LowerArray A)
    (ho : HasTreeOrderAtLeast A b (2*m)) (he : s+1+3=3*m)
    (hidden : ∀ f∈zeroSpace A 4, b*f=0 ∧ tau A b*f=0) :
    ∃ U w r, MidpointHead A m U w r := by
  obtain ⟨_,five,U,U5,UI,UM,lo,hi⟩:=quartic_rank_dispatch hm ha ho he hidden
  obtain ⟨_,_,_,_,mid,_,_⟩:=even_boundary hm ha ho he
  have ranks (j : ℕ) (a : 5≤j) (z : j≤m) : finrank K (zeroSpace A j)=j-1 := by
    have inc:=flag_gain ha ho (a:=5) (n:=j) (by decide) a (by omega)
    have dec:=flag_gain ha ho (a:=j) (n:=m) (by omega) z (by omega)
    omega
  have one (j : ℕ) (lo : 5≤j) (hi : j<m) : finrank K (zeroSpace A (j+1))≤finrank K (zeroSpace A j)+1 := by
    rw [ranks _ (by omega) (by omega),ranks _ lo (by omega)];omega
  have non (j : ℕ) (lo : 5≤j) (hi : j<m) : ¬(zeroSpace A j).map (diag (nodes A))≤zeroSpace A j := by
    intro contra
    have gr:=dirk_forward_invariant_outgoing ha ho (j:=j) (by omega) _ le_rfl (fun v hv=>contra ⟨v,hv,rfl⟩)
    have too:=one j lo hi
    omega
  obtain ⟨r,V,w,hr,VI,V5,VM,base,_,_,count,norm,_⟩:=
    Clock.ordinary_normal_head A 5 (one 5 le_rfl (by omega)) (non 5 le_rfl (by omega))
  have eqUV : U=V := le_antisymm (VM U UI U5) (UM V (V5.trans (zeroSpace_mono A (by omega))) VI)
  subst V
  refine ⟨U,w,r,hr,UI,U5,UM,lo,hi,by omega,norm,?_⟩
  intro j a z
  have hb:=Clock.ordinary_staircase (h:=m-5) UI hr base
    (fun k hk=>one (5+k) (by omega) (by omega))
    (fun k hk=>non (5+k) (by omega) (by omega)) (j-5) (by omega)
  simpa only [show 5+(j-5)=j by omega] using hb

/-- No hidden-port condition is assumed on the actual p14 and p16
equality charts: the checked original-array quartic theorems supply it. -/
theorem midpoint_head_fixed (hm : m=7 ∨ m=8) (ha : LowerArray A)
    (ho : HasTreeOrderAtLeast A b (2*m)) (he : s+1+3=3*m) :
    ∃ U w r, MidpointHead A m U w r := by
  rcases hm with rfl|rfl
  · have es:s=17:=by omega
    subst s
    exact midpoint_head_of_quartic_hidden (by decide) ha ho he (fun _ h=>order14_quartic_hidden ha ho h)
  · have es:s=20:=by omega
    subst s
    exact midpoint_head_of_quartic_hidden (by decide) ha ho he (fun _ h=>order16_quartic_hidden ha ho h)

end
end RKCert.Paired.Terminal
