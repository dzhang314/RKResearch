module
public import RKCert.LUPackedNaturals
@[expose] public section
namespace RKCert.LU
open Matrix
variable {n:ℕ}
theorem digit_zero_of_pad {x i j:ℕ}(z:x%base^i=0)(before:j < i):digit x j=0:=by
  obtain ⟨a,rfl⟩:=Nat.dvd_of_mod_eq_zero z
  have split:base^i=base^j*(base*base^(i-(j+1))):=by
    rw [←pow_succ',←pow_add];congr 1;omega
  rw [digit,split,Nat.mul_assoc,Nat.mul_div_cancel_left _ (pow_pos (by decide:0<base) _)]
  simp [Nat.mul_assoc]

/-- Certify a modular PLU determinant by just n packed integer identities.
Payload M, L, and U is dense row-major; each natural packs one full row in
base 1024, least-significant entry first. W stores a proved 32-bit-lane
scattering of U, not an assumed product. No rank or invertibility is needed:
a zero on the U diagonal is accepted. The matrix dimension bound is solely
a proved integer no-carry condition and allows several thousand rows. -/
theorem det_packed (p:ℕ)(M L U W:Array ℕ)(w:List (Fin n×Fin n))(v:ZMod p)
    (small:0<p ∧ p≤base) (room:n*((base-1)*(base-1))<wide)
    (lower:∀i:Fin n,get L i.val<base^(i.val+1) ∧ digit (get L i.val) i.val=1)
    (upper:∀i:Fin n,get U i.val%base^i.val=0)
    (scatter:∀i:Fin n,get W i.val=widen n (get U i.val))
    (product:∀i:Fin n,get M (permute w i).val=recode wide base p n (combine (get L i.val) W n))
    (value:sign (ZMod p) w*(∏i:Fin n,(digit (get U i.val) i.val:ZMod p))=v):
    (rowMatrix p n M).det=v:=by
  rw [←value];apply det_of_lu (rowMatrix p n M) (rowMatrix p n L) (rowMatrix p n U) w
  · ext i j
    change (digit (get M (permute w i).val) j.val:ZMod p)=_
    rw [product i,reduced_row_digit _ _ _ _ _ _ small room scatter,Matrix.mul_apply]
    simp only [ZMod.natCast_mod,dotAt,Nat.cast_sum,Nat.cast_mul,rowMatrix]
    rw [Finset.sum_range]
  · intro i j less;change i < j at less
    change (digit (get L i.val) j.val:ZMod p)=0
    rw [digit_zero_of_bound (lower i).1 less,Nat.cast_zero]
  · intro i j less;change j < i at less
    change (digit (get U i.val) j.val:ZMod p)=0
    rw [digit_zero_of_pad (upper i) less,Nat.cast_zero]
  · intro i;change (digit (get L i.val) i.val:ZMod p)=1
    rw [(lower i).2,Nat.cast_one]

/-- The true arbitrary matrix needs only a paid entrywise equality with the
given public concrete row-major representation. This is an adapter, not an
assumption about the determinant. -/
theorem of_rows {p:ℕ}(A:Matrix (Fin n) (Fin n) (ZMod p))(M:Array ℕ)(v:ZMod p)
    (entry:∀i j,A i j=(digit (get M i.val) j.val:ZMod p))(checked:(rowMatrix p n M).det=v):
    A.det=v:=by
  have equal:A=rowMatrix p n M:=by ext i j;exact entry i j
  rw [equal,checked]
end RKCert.LU
