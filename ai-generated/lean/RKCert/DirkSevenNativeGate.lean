module
public import RKCert.DirkSevenTransfer
public import RKCert.DirkSevenMomentRows
@[expose] public section
namespace RKCert.SevenPort
open Polynomial RKCert.Paired RKCert.Paired.Terminal
variable {K:Type*} [Field K] [CharZero K]
/-- Over every characteristic-zero field, two original chronological ports
with 3+2 primitive tests cannot coexist with six globally paid moments on
a nonzero remaining quartic factor. No real-order hypothesis. -/
theorem quartic_seven_clean (Q T:K[X])(dQ:Q.natDegree≤4)(dT:T.natDegree≤4)(nzT:T≠0)
    {u v:K}(un:u≠0)(vn:v≠0)(diff:v≠u)
    (first:∀k:Fin 3,(primitive (X^(k.val+1)*Q)).eval u=0)
    (next:∀k:Fin 2,(primitive (X^(k.val+1)*((X-C u)*Q))).eval v=0)
    (global:∀k:Fin 6,integral (X^(k.val+1)*((X-C u)*(X-C v)*Q)*T)=0):Q=0:=by
  by_contra nz
  obtain ⟨a,d,_,dn,qa,bodyEq⟩:=native_shape Q dQ nz un vn diff first next
  apply no_common_minors (15*a) u (by linear_combination 15*qa)
  apply singular_minors _ _ T dT nzT
  intro k;have h:=global k
  rw [bodyEq,show X^(k.val+1)*(C d*body (15*a) u)*T=d • (X^(k.val+1)*body (15*a) u*T) by rw [smul_eq_C_mul];ring,
      map_smul,smul_eq_mul] at h
  exact (mul_eq_zero.mp h).resolve_left dn
end RKCert.SevenPort
