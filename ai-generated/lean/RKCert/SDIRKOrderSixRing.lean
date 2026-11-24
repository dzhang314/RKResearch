module

public import RKCert.SDIRKOrderSix
public import RKCert.CharZeroTransfer

@[expose] public section
/-! # Strict SDIRK, characteristic-zero rings and the through-order-20 table
The marked-ring hypothesis is the exact condition for a simultaneous
characteristic-zero field image with nonzero shared diagonal. It holds for
every unit diagonal in any characteristic-zero commutative ring. -/
namespace RKCert.Paired.SDIRK

/-- Six is the only order ≤20 at which the strict shared diagonal currently
improves the general nonsingular triangular commutator floor. -/
def strictCharZeroFloor (p:ℕ) : ℕ := if p=6 then 7 else quadraticFloor p

theorem strict_char_zero_le20 {K : Type*} [Field K] [CharZero K] {s p:ℕ}
    {A : Fin s→Fin s→K} {b : Fin s→K} {γ:K}
    (ho : HasTreeOrderAtLeast A b p) (ha : lower A) (he : ∀i,A i i=γ)
    (hγ : γ≠0) (hp : 0<p) (h20 : p≤20) : strictCharZeroFloor p≤s := by
  by_cases h:p=6
  · subst p;exact seven_le_of_strict_order_six ho ha he hγ
  · simpa [strictCharZeroFloor,h] using
      nonsingular_quadratic_le20 ho ha (fun i=>he i ▸ hγ) hp h20

theorem seven_le_of_strict_order_six_marked_ring {R : Type*} [CommRing R] {s:ℕ}
    {A : Fin s→Fin s→R} {b : Fin s→R} {γ:R}
    (ho : HasTreeOrderAtLeast A b 6) (ha : ∀i j, i.val < j.val → A i j=0)
    (he : ∀i,A i i=γ) (hγ : ∀ n k : ℕ, 0<n → (n:R)*γ^k≠0) : 7≤s :=
  markedCommonDiagonal_of_charZero_fields
    (fun _ _ _ _ _ _ ha he hd h => seven_le_of_strict_order_six h ha he hd) ha he hγ ho

theorem seven_le_of_strict_order_six_unit_ring {R : Type*} [CommRing R] [CharZero R] {s:ℕ}
    {A : Fin s→Fin s→R} {b : Fin s→R} {γ:R}
    (ho : HasTreeOrderAtLeast A b 6) (ha : ∀i j, i.val < j.val → A i j=0)
    (he : ∀i,A i i=γ) (hγ : IsUnit γ) : 7≤s :=
  unitCommonDiagonal_of_charZero_fields
    (fun _ _ _ _ _ _ ha he hd h => seven_le_of_strict_order_six h ha he hd) ha he hγ ho

theorem strict_char_zero_marked_ring_le20 {R : Type*} [CommRing R] {s p:ℕ}
    {A : Fin s→Fin s→R} {b : Fin s→R} {γ:R}
    (ho : HasTreeOrderAtLeast A b p) (ha : ∀i j, i.val < j.val → A i j=0)
    (he : ∀i,A i i=γ) (hγ : ∀ n k : ℕ, 0<n → (n:R)*γ^k≠0) (hp : 0<p) (h20 : p≤20) :
    strictCharZeroFloor p≤s :=
  markedCommonDiagonal_of_charZero_fields
    (fun _ _ _ _ _ _ ha he hd h => strict_char_zero_le20 h ha he hd hp h20) ha he hγ ho

theorem strict_char_zero_unit_ring_le20 {R : Type*} [CommRing R] [CharZero R] {s p:ℕ}
    {A : Fin s→Fin s→R} {b : Fin s→R} {γ:R}
    (ho : HasTreeOrderAtLeast A b p) (ha : ∀i j, i.val < j.val → A i j=0)
    (he : ∀i,A i i=γ) (hγ : IsUnit γ) (hp : 0<p) (h20 : p≤20) : strictCharZeroFloor p≤s :=
  unitCommonDiagonal_of_charZero_fields
    (fun _ _ _ _ _ _ ha he hd h => strict_char_zero_le20 h ha he hd hp h20) ha he hγ ho

theorem strict_char_zero_table : (List.range 20).map (fun k=>strictCharZeroFloor (k+1)) =
    [1,1,2,3,5,7,8,10,13,15,18,21,25,28,32,36,41,45,50,55] := by decide

end RKCert.Paired.SDIRK
