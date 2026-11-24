module
public import RKCert.DirkQuinticTransfer
public import RKCert.DirkQ9Table
@[expose] public section
namespace RKCert.Paired
open RKCert.DirkQuintic
variable {K:Type*} [Field K] [CharZero K] {s p:ℕ} {A:Fin s→Fin s→K} {b:Vec K s}
/-- An order-18 lower-triangular method over an arbitrary characteristic-zero
field requires at least 25 physical stages. -/
theorem dirk_order18_charZero_field (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b p)
    (hp:18≤p) : 25≤s := by
  have paid:HasTreeOrderAtLeast A b (2*9):=fun t ht=>ho t (ht.trans hp)
  exact from_fixed_grid (m:=9) (Or.inl rfl) ha paid degree_grid9 sep_grid9
    (specialization9 (check_grid_int integers9 grid9 map_integers9 checked_int9))
end RKCert.Paired
namespace RKCert
universe u
/-- Ring form of the characteristic-zero order-18 exclusion. -/
theorem dirk_order18_charZero_ring {R:Type u} [CommRing R] [CharZero R] {s p:ℕ}
    {A:Fin s→Fin s→R} {b:Fin s→R} (ha:∀i j:Fin s,i.val<j.val → A i j=0)
    (ho:HasTreeOrderAtLeast A b p) (hp:18≤p) : 25≤s :=
  lowerTriangular_of_charZero_fields
    (fun _ _ _ _ _ ht hs=>Paired.dirk_order18_charZero_field ht hs hp) ha ho
end RKCert

