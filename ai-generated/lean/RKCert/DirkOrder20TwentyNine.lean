module
public import RKCert.DirkTwentyHiddenSix
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
@[expose] public section
namespace RKCert.Paired
open Terminal
variable {K:Type*} [Field K] [CharZero K] {s p:ℕ} {A:Fin s→Fin s→K} {b:Vec K s}

/-- Every lower-triangular tableau of all-tree order at least twenty over
an arbitrary characteristic-zero field has at least twenty-nine stages. -/
theorem dirk_order20_twenty_nine_charZero_field (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b p)
    (hp:20≤p):29≤s:=by
  have paid:HasTreeOrderAtLeast A b 20:=fun t ht=>ho t (ht.trans hp)
  have floor:=twenty_floor_from_grade_ten ha paid
  by_contra! short
  cases s with
  | zero=>omega
  | succ n=>
    let φ:K→+*AlgebraicClosure K:=algebraMap K (AlgebraicClosure K)
    exact twenty_eight_impossible (lowerTriangular_map ha φ) (paid.map φ) (by omega) (IsAlgClosed.splits _)
end RKCert.Paired
namespace RKCert
universe u
/-- Field/ring transfer preserves all original stages and imposes neither
a chosen order nor a division or nonzero weight on the source ring. -/
theorem dirk_order20_twenty_nine_charZero_ring {R:Type u} [CommRing R] [CharZero R] {s p:ℕ}
    {A:Fin s→Fin s→R} {b:Fin s→R} (ha:∀i j:Fin s,i.val<j.val→A i j=0)
    (ho:HasTreeOrderAtLeast A b p) (hp:20≤p):29≤s:=
  lowerTriangular_of_charZero_fields
    (fun _ _ _ _ _ ht hs=>Paired.dirk_order20_twenty_nine_charZero_field ht hs hp) ha ho
end RKCert
