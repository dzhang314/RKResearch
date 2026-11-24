module

public import RKCert.Dirk15NonC2FullFlag
public import RKCert.Dirk15HideCubic

@[expose] public section

/-! # Genuine ordinary core in the minimal marked order-fifteen chart

This is a native rank reduction, not a stage bound. The support subspace
retains the original first physical row and every zero-weight row.
-/
namespace RKCert.Paired
open Module RKCert.OneEscape
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [CharZero K]
variable {A : Fin 20 → Fin 20 → K} {b : Vec K 20}

theorem order15_grade5_unit_no_hyperplane (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    {U : Submodule K (Vec K 20)} (inv : U.map (diag (nodes A)) ≤ U)
    (in5 : U ≤ zeroSpace A 5)
    (r5 : finrank K (zeroSpace A 5) = finrank K U + 1)
    (unit : ∀ j : ℕ, 5 ≤ j → j ≤ 6 →
      finrank K (zeroSpace A (j+1)) = finrank K (zeroSpace A j)+1) : False := by
  have step (k : ℕ) (hk : k<2) :
      finrank K (zeroSpace A (5+k+1))≤finrank K (zeroSpace A (5+k))+1 ∧
        ¬(zeroSpace A (5+k)).map (diag (nodes A))≤zeroSpace A (5+k) := by
    have hu := unit (5+k) (by omega) (by omega)
    refine ⟨hu.le,fun i => ?_⟩
    have h := dirk_forward_invariant_outgoing ha ho (j:=5+k) (by omega)
      (zeroSpace A (5+k)) le_rfl (fun v hv => i (Submodule.mem_map_of_mem hv))
    omega
  obtain ⟨r,V,w,rp,_,_,maxV,base,_,_,rd⟩ :=
    Clock.ordinary_single_head A 5 (step 0 (by decide)).1 (step 0 (by decide)).2
  have le : U≤V := maxV U inv in5
  have dim := Submodule.finrank_mono le
  have eq : U=V := Submodule.eq_of_le_of_finrank_le le (by omega)
  subst V
  have r1 : r=1 := by omega
  subst r
  exact no_invariant_grade5_head ha ho (by decide) inv in5
    (Clock.ordinary_staircase inv (by decide) base (fun k hk => (step k hk).1)
      (fun k hk => (step k hk).2))

structure Order15MinimalHead (A : Fin 20 → Fin 20 → K) (b : Vec K 20) where
  U : Submodule K (Vec K 20)
  w : Vec K 20
  maximal : MaximalClockCore A 7 U
  low : 1 ≤ finrank K U
  high : finrank K U ≤ 2
  ghosts : simultaneousGhosts A b ≤ U
  cubic : zeroSpace A 3 ≤ simultaneousGhosts A b
  six : zeroSpace A 6 = chain (diag (nodes A)) U w (5-finrank K U)
  seven : zeroSpace A 7 = chain (diag (nodes A)) U w (6-finrank K U)
  seven_escape : ¬(zeroSpace A 7).map (diag (nodes A)) ≤ zeroSpace A 7

/-- Nature supplies the common maximal core and the cheap head powers in
F6, with no premise on F4, F5, or on a projected tableau. -/
theorem order15_minimal_head (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (H : Order15MinimalMarkedChart A b) : Nonempty (Order15MinimalHead A b) := by
  obtain ⟨U,hU⟩ := order15_nonC2_has_core (A:=A)
  have r3 : finrank K (zeroSpace A 3)=1 := H.initial.f3
  have r6 : finrank K (zeroSpace A 6)=5 := H.initial.f6
  have r7 : finrank K (zeroSpace A 7)=6 := H.initial.f7
  obtain ⟨u6,high,hhigh⟩ := order15_ordinary_core_rank ha ho (e:=0) r3 r6 r7 U hU
  have hlarge : finrank K U ≠ 3 := by
    intro rU
    obtain ⟨inc,r5⟩ := hhigh rU
    exact order15_grade5_unit_no_hyperplane ha ho hU.2.1 inc (by omega)
      (fun j lo hi => by
        rcases (show j=5 ∨ j=6 by omega) with rfl|rfl
        · change finrank K (zeroSpace A 6)=finrank K (zeroSpace A 5)+1; omega
        · change finrank K (zeroSpace A 7)=finrank K (zeroSpace A 6)+1; omega)
  have cap : finrank K U ≤ 2 := by omega
  have first := order15_minimal_reverse_nonlocal ha ho H
  have ghosts := hU.2.2 _ (order15_simultaneous_ghosts_le ha ho H first) simultaneousGhosts_invariant
  have cubic := order15_cubic_le_simultaneous_ghosts ha ho H first
  have dm := Submodule.finrank_mono (cubic.trans ghosts)
  have low : 1 ≤ finrank K U := by omega
  have escape6 : ¬(zeroSpace A 6).map (diag (nodes A))≤zeroSpace A 6 := by
    intro i
    have e := dirk_forward_invariant_outgoing ha ho (j:=6) (by decide)
      (zeroSpace A 6) le_rfl (fun v hv => i (Submodule.mem_map_of_mem hv))
    change finrank K (zeroSpace A 6)+3≤finrank K (zeroSpace A 7) at e
    omega
  have escape7 : ¬(zeroSpace A 7).map (diag (nodes A))≤zeroSpace A 7 := by
    intro i
    have e := dirk_forward_invariant_incoming ha ho (j:=7) (by decide)
      (fun v hv => i (Submodule.mem_map_of_mem hv))
    change finrank K (zeroSpace A 6)+3≤finrank K (zeroSpace A 7) at e
    omega
  have one : finrank K (zeroSpace A (6+1))≤finrank K (zeroSpace A 6)+1 := by
    change finrank K (zeroSpace A 7)≤finrank K (zeroSpace A 6)+1
    omega
  obtain ⟨d,V,w,dp,inv,in6,maxV,base,_,_,rd⟩ :=
    Clock.ordinary_single_head A 6 one escape6
  have e : V=U := le_antisymm
    (hU.2.2 _ (in6.trans (zeroSpace_mono A (by decide))) inv)
    (maxV U hU.2.1 u6)
  subst V
  have dd : d=5-finrank K U := by omega
  have e7 := Clock.ordinary_step one escape6
  rw [base,chain_sup_map hU.2.1 dp] at e7
  rw [dd] at base e7
  have er : (5-finrank K U)+1=6-finrank K U := by omega
  rw [er] at e7
  exact ⟨⟨U,w,hU,low,cap,ghosts,cubic,base,e7,escape7⟩⟩

omit [CharZero K] in
theorem Order15MinimalHead.two_hidden_rank (h : Order15MinimalHead A b)
    (H : Order15MinimalMarkedChart A b) (f34 : zeroSpace A 3 < zeroSpace A 4)
    (h4 : zeroSpace A 4 ≤ simultaneousGhosts A b) :
    zeroSpace A 4 = simultaneousGhosts A b ∧ simultaneousGhosts A b=h.U ∧ finrank K h.U=2 := by
  have lt := Submodule.finrank_lt_finrank_of_lt f34
  have r3 := H.initial.f3
  have i4 := Submodule.finrank_mono h4
  have gU := Submodule.finrank_mono h.ghosts
  have u2 := h.high
  exact ⟨Submodule.eq_of_le_of_finrank_le h4 (by omega),
    Submodule.eq_of_le_of_finrank_le h.ghosts (by omega),by omega⟩

end
end RKCert.Paired
