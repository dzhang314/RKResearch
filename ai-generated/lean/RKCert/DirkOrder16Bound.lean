module
public import RKCert.DirkMidpointTwoHead
public import RKCert.DirkMidpointSingleton16
@[expose] public section
namespace RKCert.Paired.Terminal
open Polynomial Module RKCert.OneEscape
variable {K:Type*} [Field K] [CharZero K] {s:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}

/-- The only remaining order-14 equality branch has one paid head at five
and already has a genuinely disjoint multiplicatively closed core. -/
theorem order14_remaining_singleton (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 14)
    (he:s+1+3=3*7) : ∃ U w, MidpointHead A 7 U w 1 ∧
      (∀i,Clock.Live U i→w i=0) ∧ Clock.MulClosed U :=by
  obtain ⟨U,w,r,h⟩:=midpoint_head_fixed (m:=7) (Or.inl rfl) ha ho he
  obtain ⟨w',h',cut,mul⟩:=h.disjoint_midpoint_head (Or.inl rfl) ha ho he
  rcases (show r=1 ∨ r=2 by have:=h.count;have:=h.lower;have:=h.upper;have:=h.positive;omega) with rfl|rfl
  · exact ⟨U,w',h',cut,mul⟩
  · exact (h'.no_two_head (Or.inl rfl) ha ho he cut mul).elim

theorem order16_boundary_empty (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 16)
    (he:s+1+3=3*8) : False:=by
  obtain ⟨U,w,r,h⟩:=midpoint_head_fixed (m:=8) (Or.inr rfl) ha ho he
  obtain ⟨w',h',cut,mul⟩:=h.disjoint_midpoint_head (Or.inr rfl) ha ho he
  rcases (show r=1 ∨ r=2 by have:=h.count;have:=h.lower;have:=h.upper;have:=h.positive;omega) with rfl|rfl
  · exact h'.no_single_head16 ha ho he cut mul
  · exact h'.no_two_head (Or.inr rfl) ha ho he cut mul

end RKCert.Paired.Terminal
namespace RKCert.Paired
variable {K:Type*} [Field K] [CharZero K] {s p:ℕ} {A:Fin s→Fin s→K} {b:Vec K s}
/-- Order sixteen requires at least 22 original physical stages over
every characteristic-zero field. No ordering hypothesis is required. -/
theorem dirk_order16_charZero_field (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b p)
    (hp:16≤p) : 22≤s:=by
  have h16:HasTreeOrderAtLeast A b 16:=fun t ht=>ho t (ht.trans hp)
  have floor:=(Terminal.even_floor (m:=8) (by decide) ha h16).1
  by_contra! short
  cases s with
  | zero=>omega
  | succ s=> exact Terminal.order16_boundary_empty ha h16 (by omega)
end RKCert.Paired
namespace RKCert
universe u
theorem dirk_order16_charZero_ring {R:Type u} [CommRing R] [CharZero R] {s p:ℕ}
    {A:Fin s→Fin s→R} {b:Fin s→R} (ha:∀i j:Fin s,i.val<j.val → A i j=0)
    (ho:HasTreeOrderAtLeast A b p) (hp:16≤p) : 22≤s :=
  lowerTriangular_of_charZero_fields
    (fun _ _ _ _ _ ht hs=>Paired.dirk_order16_charZero_field ht hs hp) ha ho
end RKCert

