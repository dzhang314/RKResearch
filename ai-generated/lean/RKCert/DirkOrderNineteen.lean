module
public import RKCert.Dirk19PaidKernel
public import RKCert.Dirk19TerminalSlice
@[expose] public section
namespace RKCert.Paired
open Module Terminal
variable {K:Type*} [Field K] [CharZero K]

/-- No order-nineteen ordinary lower triangular tableau has 26 actual stages.
No order, positivity, nonzero diagonal or simplifying condition on the field
or tableau is assumed. -/
theorem Nineteen.no_twenty_six {A:Fin 26→Fin 26→K} {b:Vec K 26}
    (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 19) : False:=by
  obtain ⟨W,low,high,iw⟩:=Nineteen.hidden_space ha ho
  have R:=Nineteen.initial_ranks ha ho
  obtain ⟨_,_,U,w,r,short,iu,_,band⟩:=nine_rank_dispatch ha ho (by decide)
    R.f3.ge R.f5_upper R.f6.ge R.f9 R.f10.le low high iw
  obtain ⟨_,escape,products⟩:=Nineteen.raised_nine_slice ha ho
  exact no_nine_short_head ha ho (by decide) short iu band escape products

/-- Physical order at least 19 forces at least 27 stages in an arbitrary
characteristic-zero field. -/
theorem dirk_order19_charZero_field {s p:ℕ} {A:Fin s→Fin s→K} {b:Vec K s}
    (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b p) (hp:19≤p):27≤s:=by
  have pay:HasTreeOrderAtLeast A b 19:=fun t ht=>ho t (ht.trans hp)
  have prior:=odd_floor (m:=9) (by decide) ha pay
  by_contra! small
  have eqn:s=26:=by omega
  subst s
  exact Nineteen.no_twenty_six ha pay
end RKCert.Paired
namespace RKCert
universe u
/-- The same order-nineteen floor over any commutative characteristic-zero ring,
including rings with zero divisors. -/
theorem dirk_order19_charZero_ring {R:Type u} [CommRing R] [CharZero R] {s p:ℕ}
    {A:Fin s→Fin s→R} {b:Fin s→R} (ha:∀i j:Fin s,i.val<j.val → A i j=0)
    (ho:HasTreeOrderAtLeast A b p) (hp:19≤p):27≤s:=
  lowerTriangular_of_charZero_fields
    (fun _ _ _ _ _ ht hs=>Paired.dirk_order19_charZero_field ht hs hp) ha ho
end RKCert
