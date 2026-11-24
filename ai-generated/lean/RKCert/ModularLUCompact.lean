module
public import RKCert.ModularLUPacked
@[expose] public section
namespace RKCert.LU
open Matrix
variable {n:ℕ}

def scattered (n:ℕ)(U:Array ℕ):Array ℕ:=U.map (widen n)
theorem widen_zero (n:ℕ):widen n 0=0:=by
  rw [widen_pack];simp [pack,digit]
theorem get_scattered (n:ℕ)(U:Array ℕ)(i:ℕ):get (scattered n U) i=widen n (get U i):=by
  simp only [get,scattered,Array.getElem?_map]
  cases U[i]? with
  | none=>simp [widen_zero]
  | some x=>rfl

/-- Smaller certificates omit the public scattered rows: the verified kernel
can construct them from the original compact U. -/
theorem det_packed_compact (p:ℕ)(M L U:Array ℕ)(w:List (Fin n×Fin n))(v:ZMod p)
    (small:0<p ∧ p≤base) (room:n*((base-1)*(base-1))<wide)
    (lower:∀i:Fin n,get L i.val<base^(i.val+1) ∧ digit (get L i.val) i.val=1)
    (upper:∀i:Fin n,get U i.val%base^i.val=0)
    (product:∀i:Fin n,get M (permute w i).val=recode wide base p n (combine (get L i.val) (scattered n U) n))
    (value:sign (ZMod p) w*(∏i:Fin n,(digit (get U i.val) i.val:ZMod p))=v):
    (rowMatrix p n M).det=v:=
  det_packed p M L U (scattered n U) w v small room lower upper (fun i=>get_scattered n U i.val) product value

/-- Change both finite index types together. Concrete verified rows can be
used with arbitrary subset-indexed, compound, and block-Gram matrices. -/
theorem of_rows_equiv {p:ℕ}{ι:Type*} [Fintype ι] [DecidableEq ι] (A:Matrix ι ι (ZMod p))
    (e:Fin n≃ι)(M:Array ℕ)(v:ZMod p)
    (entry:∀i j,A (e i) (e j)=(digit (get M i.val) j.val:ZMod p))
    (checked:(rowMatrix p n M).det=v):A.det=v:=by
  rw [←Matrix.det_submatrix_equiv_self e A]
  exact of_rows _ M v entry checked
end RKCert.LU
