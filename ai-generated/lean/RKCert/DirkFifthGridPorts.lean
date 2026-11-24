module
public import RKCert.DirkFifthGridMinor
public import RKCert.DirkFifthAlgebra
@[expose] public section
namespace RKCert.PaidFifth
open Polynomial RKCert.Paired RKCert.Paired.Terminal
variable {K:Type*} [Field K] [CharZero K]

/-- Genuinely unequal 3+2 primitives at two active fixed knots plus a
single omitted third knot kill an arbitrary quintic; no order or sign. -/
theorem lobatto10_omitted_quintic {u v z:K}
    (gu:((X-1)*lobatto 10).eval u=0) (gv:((X-1)*lobatto 10).eval v=0)
    (gz:((X-1)*lobatto 10).eval z=0) (un:u≠0) (vn:v≠0)
    (vu:v≠u) (zu:z≠u) (zv:z≠v) (P:K[X]) (degree:P.natDegree≤5) (root:P.eval z=0)
    (first:∀k:Fin 3,(primitive (X^(k.val+1)*P)).eval u=0)
    (next:∀k:Fin 2,(primitive (X^(k.val+1)*((X-C u)*P))).eval v=0):P=0:=by
  let w:Fin 3→K:=![u,v,z]
  have roots(i:Fin 3):((X-1)*lobatto 10).eval (w i)=0:=by fin_cases i <;> first | exact gu | exact gv | exact gz
  have inj:Function.Injective w:=by
    intro i j e
    fin_cases i <;> fin_cases j <;> first
      | rfl
      | exact False.elim (vu e)
      | exact False.elim (vu e.symm)
      | exact False.elim (zu e) | exact False.elim (zu e.symm) | exact False.elim (zv e) | exact False.elim (zv e.symm)
  exact quintic_ports un vn vu (grid_minor w roots inj) P degree root first next

end RKCert.PaidFifth
