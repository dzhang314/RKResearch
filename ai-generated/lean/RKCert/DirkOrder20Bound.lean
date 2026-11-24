module
public import RKCert.DirkQuinticTransfer
public import RKCert.DirkQ10Table
@[expose] public section
namespace RKCert.Paired
open RKCert.DirkQuintic
variable {K:Type*} [Field K] [CharZero K] {s p:ℕ} {A:Fin s→Fin s→K} {b:Vec K s}
/-- An order-20 lower-triangular method over an arbitrary characteristic-zero
field requires at least 28 physical stages. -/
theorem dirk_order20_charZero_field (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b p)
    (hp:20≤p) : 28≤s := by
  have paid:HasTreeOrderAtLeast A b (2*10):=fun t ht=>ho t (ht.trans hp)
  exact from_fixed_grid (m:=10) (Or.inr rfl) ha paid degree_grid10 sep_grid10
    (specialization10 (check_grid_int integers10 grid10 map_integers10 checked_int10))
end RKCert.Paired
namespace RKCert
universe u
/-- Ring form of the characteristic-zero order-20 exclusion. -/
theorem dirk_order20_charZero_ring {R:Type u} [CommRing R] [CharZero R] {s p:ℕ}
    {A:Fin s→Fin s→R} {b:Fin s→R} (ha:∀i j:Fin s,i.val<j.val → A i j=0)
    (ho:HasTreeOrderAtLeast A b p) (hp:20≤p) : 28≤s :=
  lowerTriangular_of_charZero_fields
    (fun _ _ _ _ _ ht hs=>Paired.dirk_order20_charZero_field ht hs hp) ha ho
end RKCert

