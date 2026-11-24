module
public import RKCert.DirkOrder16Bound
public import RKCert.FiveDebutObstruction
@[expose] public section
namespace RKCert.Paired.Terminal
open Module RKCert.OneEscape
variable {K:Type*} [Field K] [CharZero K] {s:ℕ} {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
theorem order14_boundary_empty (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 14)
    (he:s+1+3=3*7) : False:=by
  obtain ⟨U,w,h,_,mul⟩:=order14_remaining_singleton ha ho he
  apply RKCert.FiveDebut.no_grade5_head ha ho (by decide) h.invariant mul h.paid (w:=w)
  intro k hk
  simpa using h.band (5+k) (by omega) (by omega)
end RKCert.Paired.Terminal
namespace RKCert.Paired
variable {K:Type*} [Field K] [CharZero K] {s p:ℕ} {A:Fin s→Fin s→K} {b:Vec K s}
theorem dirk_order14_charZero_field (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b p)
    (hp:14≤p) : 19≤s:=by
  have h14:HasTreeOrderAtLeast A b 14:=fun t ht=>ho t (ht.trans hp)
  have lower:=(Terminal.even_floor (m:=7) (by decide) ha h14).1
  by_contra! short
  cases s with
  | zero=>omega
  | succ s=>exact Terminal.order14_boundary_empty ha h14 (by omega)
end RKCert.Paired
namespace RKCert
universe u
theorem dirk_order14_charZero_ring {R:Type u} [CommRing R] [CharZero R] {s p:ℕ}
    {A:Fin s→Fin s→R} {b:Fin s→R} (ha:∀i j:Fin s,i.val<j.val → A i j=0)
    (ho:HasTreeOrderAtLeast A b p) (hp:14≤p) : 19≤s :=
  lowerTriangular_of_charZero_fields (fun _ _ _ _ _ ht hs=>Paired.dirk_order14_charZero_field ht hs hp) ha ho
end RKCert

