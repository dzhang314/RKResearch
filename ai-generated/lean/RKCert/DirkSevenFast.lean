module
public import RKCert.DirkSevenResidue
public import Mathlib.LinearAlgebra.Matrix.Block
@[expose] public section
namespace RKCert.SevenPort
open Polynomial Matrix RKCert.FixedFactor
set_option maxRecDepth 3000
def lookup (l:List ℕ)(n:ℕ):E:=(l[n]?.getD 0:ℕ)
def low (l:List ℕ):Matrix (Fin 5) (Fin 5) E:=fun i j=>
  if i=j then 1 else if i<j then 0 else lookup l (i.val*(i.val-1)/2+j.val)
/-- An LDLᵀ certificate verifies a complete Hankel determinant with 25 short dot products
and ten independent true moments; no untrusted computation enters the kernel. -/
theorem check_ldl (t u:E)(k:ℕ)(hk:k≤1)(e l d:List ℕ)(v:E)
    (ecert:∀n:Fin 10,entry t u n.val=lookup e n.val)
    (fact:∀i j:Fin 5,lookup e (k+i.val+j.val)=∑h:Fin 5,low l i h*lookup d h.val*low l j h)
    (value:(∏h:Fin 5,lookup d h.val)=v):d5 t u k=v:=by
  let L:=low l
  let D:=diagonal (fun h:Fin 5=>lookup d h.val)
  have lowL:L.IsLowerTriangular:=by
    intro i j ij
    change i<j at ij
    simp [L,low,ne_of_lt ij,ij]
  have unit:L.det=1:=by rw [det_of_isLowerTriangular _ lowL];simp [L,low]
  have eqn:matrix t u k=L*D*L.transpose:=by
    ext i j
    change entry t u (k+i.val+j.val)=_
    rw [ecert ⟨k+i.val+j.val,by have:=i.isLt;have:=j.isLt;omega⟩,fact]
    rw [Matrix.mul_apply]
    simp only [D,Matrix.mul_diagonal,Matrix.transpose_apply,L]
  rw [d5,eqn,det_mul,det_mul,det_transpose,unit,one_mul,mul_one,det_diagonal,value]
theorem fits_offset (t:E)(k:ℕ)(xs:List ℤ)(d:xs.length≤31)
    (checks:∀i:Fin 31,d5 t ((i.val:E)+2) k=horner xs ((i.val:E)+2)):
    minPoly t k=mp xs:=by
  apply sub_eq_zero.mp
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero (minPoly t k-mp xs)
    (show Function.Injective (fun i:Fin 31=>(i.val:E)+2) from fun i j eqn=>injective_sample _ (by decide) (add_right_cancel eqn))
  · intro i;rw [eval_sub,eval_minor,horner_sound,checks,sub_self]
  · have a:=degree_minor t k
    have b:(mp xs).natDegree≤30:=natDegree_map_le.trans (degree_horner_le _ _ d)
    have c:=natDegree_sub_le (minPoly t k) (mp xs);simp only [Fintype.card_fin];omega
end RKCert.SevenPort
