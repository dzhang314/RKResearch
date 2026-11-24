module
public import RKCert.DirkEvenCore
@[expose] public section
namespace RKCert.Paired.Terminal
open Module RKCert.OneEscape
variable {K:Type*} [Field K] {s m:ℕ} {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
noncomputable section

def jointKernel (A:Fin (s+1)→Fin (s+1)→K) (b:Vec K (s+1)) :Submodule K (Vec K (s+1)) :=
  (LinearMap.ker (LinearMap.proj 0) ⊓ LinearMap.ker (diag b)) ⊓ LinearMap.ker (diag (tau A b))

theorem joint_iff {v:Vec K (s+1)} : v∈jointKernel A b ↔ (v 0=0 ∧ b*v=0) ∧ tau A b*v=0 := Iff.rfl

theorem invariant_joint : (jointKernel A b).map (diag (nodes A))≤jointKernel A b := by
  rintro _ ⟨v,hv,rfl⟩
  obtain ⟨⟨v0,bc⟩,tc⟩:=joint_iff.mp hv
  apply joint_iff.mpr
  refine ⟨⟨by rw [diag_apply,v0,mul_zero],?_⟩,?_⟩
  · change b*(nodes A*v)=0;rw [mul_left_comm,bc,mul_zero]
  · change tau A b*(nodes A*v)=0;rw [mul_left_comm,tc,mul_zero]

variable [CharZero K]

theorem joint_sub_core (hm:7≤m) (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b (2*m)) (he:s+1+3=3*m)
    {U:Submodule K (Vec K (s+1))}
    (maximal:∀W:Submodule K (Vec K (s+1)),W≤zeroSpace A m → W.map (diag (nodes A))≤W → W≤U) :
    jointKernel A b≤U := by
  apply maximal _ _ invariant_joint
  intro v hv
  obtain ⟨⟨z,hb⟩,ht⟩:=joint_iff.mp hv
  exact zeroSpace_mono A (by omega) (joint_kernel_in_defect hm ha ho he z hb ht)

theorem hidden_to_joint (hm:7≤m) (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b (2*m)) (he:s+1+3=3*m)
    {j:ℕ} (hidden:∀v∈zeroSpace A j,b*v=0 ∧ tau A b*v=0) :
    zeroSpace A j≤jointKernel A b := fun v hv=>joint_iff.mpr
      ⟨⟨zeroSpace_first_of_row (even_boundary hm ha ho he).1 j hv,(hidden v hv).1⟩,(hidden v hv).2⟩

/-- A hidden grade five is impossible on *every* native even boundary:
the invariant core has at most three dimensions, yet a fully hidden F5
would have to equal that core and pay a two-dimensional incoming gain. -/
theorem fifth_not_hidden (hm:7≤m) (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b (2*m)) (he:s+1+3=3*m) :
    ¬∀v∈zeroSpace A 5,b*v=0 ∧ tau A b*v=0 := by
  intro hidden
  obtain ⟨U,_,hi,largest,small⟩:=even_core_three hm ha ho he
  have sub:zeroSpace A 5≤U:=(hidden_to_joint hm ha ho he hidden).trans (joint_sub_core hm ha ho he largest)
  have rank3:finrank K (zeroSpace A 3)=1:=(even_boundary hm ha ho he).2.1
  have r4:=flag_gain ha ho (a:=3) (n:=4) (by decide) (by decide) (by omega)
  have r5:=flag_gain ha ho (a:=3) (n:=5) (by decide) (by decide) (by omega)
  have lim:=Submodule.finrank_mono sub
  have eqn:zeroSpace A 5=U:=Submodule.eq_of_le_of_finrank_le sub (by omega)
  have inv:(zeroSpace A 5).map (diag (nodes A))≤zeroSpace A 5:=eqn ▸ hi
  have grow:=dirk_forward_invariant_incoming ha ho (j:=5) (by omega) (fun x hx=>inv ⟨x,hx,rfl⟩)
  change finrank K (zeroSpace A 4)+2≤finrank K (zeroSpace A 5) at grow
  omega

/-- Once grade four is paid, the genuine rank pattern is decided, and
the same maximal invariant subspace lies inside grade five. -/
theorem quartic_rank_dispatch (hm:7≤m) (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b (2*m))
    (he:s+1+3=3*m) (hidden:∀v∈zeroSpace A 4,b*v=0 ∧ tau A b*v=0) :
    finrank K (zeroSpace A 4)=2 ∧ finrank K (zeroSpace A 5)=4 ∧
    ∃U:Submodule K (Vec K (s+1)),U≤zeroSpace A 5 ∧ U.map (diag (nodes A))≤U ∧
      (∀W:Submodule K (Vec K (s+1)),W≤zeroSpace A m → W.map (diag (nodes A))≤W → W≤U) ∧
      2≤finrank K U ∧ finrank K U≤3 := by
  obtain ⟨U,um,ui,largest,small⟩:=even_core_three hm ha ho he
  have h4:=hidden_to_joint hm ha ho he hidden
  have ju:=joint_sub_core hm ha ho he largest
  have f4:=h4.trans ju
  obtain ⟨_,r3,r6,_,rm,_⟩:=even_boundary hm ha ho he
  have g3:=flag_gain ha ho (a:=3) (n:=4) (by decide) (by decide) (by omega)
  have g4:=flag_gain ha ho (a:=4) (n:=5) (by decide) (by decide) (by omega)
  have g5:=flag_gain ha ho (a:=5) (n:=6) (by decide) (by decide) (by omega)
  have u4:=Submodule.finrank_mono f4
  have f4n:finrank K (zeroSpace A 4)=2 := by
    by_contra e
    have e':zeroSpace A 4=U:=Submodule.eq_of_le_of_finrank_le f4 (by omega)
    have iv:(zeroSpace A 4).map (diag (nodes A))≤zeroSpace A 4:=e' ▸ ui
    have gr:=dirk_forward_invariant_outgoing ha ho (j:=4) (by omega) (zeroSpace A 4) le_rfl (fun v hv=>iv ⟨v,hv,rfl⟩)
    change finrank K (zeroSpace A 4)+2≤finrank K (zeroSpace A 5) at gr
    omega
  have f5n:finrank K (zeroSpace A 5)=4 := by
    by_contra ne
    have lim:finrank K (zeroSpace A 5)≤finrank K (zeroSpace A 4)+1:=by omega
    have esc:¬(zeroSpace A 4).map (diag (nodes A))≤zeroSpace A 4 := by
      intro iv
      have grow:=dirk_forward_invariant_outgoing ha ho (j:=4) (by omega) (zeroSpace A 4) le_rfl (fun v hv=>iv ⟨v,hv,rfl⟩)
      change finrank K (zeroSpace A 4)+2≤finrank K (zeroSpace A 5) at grow
      omega
    have f5:zeroSpace A 5≤jointKernel A b:=by
      rw [show 5=4+1 by decide,Clock.ordinary_step lim esc]
      exact sup_le h4 ((Submodule.map_mono h4).trans invariant_joint)
    apply fifth_not_hidden hm ha ho he
    intro v hv
    have h:=joint_iff.mp (f5 hv)
    exact ⟨h.1.2,h.2⟩
  have escape:¬zeroSpace A 5≤U := fun e=>by have:=Submodule.finrank_mono e;omega
  have quota:=terminal_quotient_growth (diag (nodes A)) (zeroSpace A)
    (fun _ _ h=>zeroSpace_mono A h) (fun j=>Submodule.map_le_iff_le_comap.mpr (diag_zeroSpace A j))
    um ui largest (by omega:5≤m) escape
  have eqn:zeroSpace A 5=zeroSpace A 5 ⊔ U:=Submodule.eq_of_le_of_finrank_le le_sup_left (by omega)
  exact ⟨f4n,f5n,U,le_sup_right.trans (le_of_eq eqn.symm),ui,largest,by omega,small⟩
end
end RKCert.Paired.Terminal

namespace RKCert.Paired
variable {K:Type*} [Field K] [CharZero K] {s m:ℕ} {A:Fin s→Fin s→K} {b:Vec K s}

/-- Every characteristic-zero lower triangular order-2m tableau with m≥11
costs at least 3m−2 physical stages. No order of the scalar field is needed. -/
theorem dirk_even_three_m_minus_two (hm:11≤m) (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b (2*m)) :
    3*m-2≤s := by
  have old:=(Terminal.even_floor (by omega) ha ho).1
  by_contra! short
  cases s with
  | zero=>omega
  | succ s=>
    have same:s+1+3=3*m:=by omega
    apply Terminal.fifth_not_hidden (by omega) ha ho same
    intro v hv
    exact Terminal.even_grade_hidden (by omega) ha ho same (by decide) (by omega) hv
end RKCert.Paired

namespace RKCert
universe u
/-- The same strengthened even-order family over arbitrary commutative
characteristic-zero rings, by the certified prime-field transfer. -/
theorem dirk_even_three_m_minus_two_ring {R:Type u} [CommRing R] [CharZero R] {s m:ℕ}
    {A:Fin s→Fin s→R} {b:Fin s→R} (hm:11≤m)
    (ha:∀i j:Fin s,i.val<j.val → A i j=0) (ho:HasTreeOrderAtLeast A b (2*m)) : 3*m-2≤s :=
  lowerTriangular_of_charZero_fields (fun _ _ _ _ _ hA hb=>Paired.dirk_even_three_m_minus_two hm hA hb) ha ho
end RKCert
