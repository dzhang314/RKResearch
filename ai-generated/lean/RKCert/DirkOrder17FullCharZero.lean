module
public import RKCert.Dirk17NoMinimalCharZero
public import RKCert.DirkOrder17TwentyFour
@[expose] public section
namespace RKCert.Paired
open Module Terminal
variable {K:Type*} [Field K] [CharZero K] {s p:ℕ} {A:Fin s→Fin s→K} {b:Vec K s}
/-- Every unrestricted lower-triangular tableau of full rooted-tree order
at least seventeen requires 24 original physical stages. There is no scalar
exception, field order, positivity, or algebraic-closure hypothesis. -/
theorem dirk_order17_twenty_four_charZero_field (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b p)
    (hp:17≤p):24≤s:=by
  have paid:HasTreeOrderAtLeast A b 17:=fun t ht=>ho t (ht.trans hp)
  have floor:=odd_floor (m:=8) (by decide) ha paid
  by_contra! short
  have eq:s=23:=by omega
  subst s
  have anc:=Seventeen.no_nonC2 ha paid
  by_cases low:finrank K (marked A 17 5)≤3
  · exact Seventeen.no_minimal_charZero ha paid anc low
  · exact Seventeen.no_early ha paid anc (by omega)
end RKCert.Paired
namespace RKCert
universe u
/-- Characteristic-zero commutative-ring version. Mapping the actual all-tree
array into a characteristic-zero field preserves its entire original width. -/
theorem dirk_order17_twenty_four_charZero_ring {R:Type u} [CommRing R] [CharZero R] {s p:ℕ}
    {A:Fin s→Fin s→R} {b:Fin s→R} (ha:∀i j:Fin s,i.val<j.val→A i j=0)
    (ho:HasTreeOrderAtLeast A b p) (hp:17≤p):24≤s:=
  lowerTriangular_of_charZero_fields
    (fun _ _ _ _ _ ht hs=>Paired.dirk_order17_twenty_four_charZero_field ht hs hp) ha ho
end RKCert
