module
public import RKCert.PortFactorGrid
public import RKCert.PortNativeConditional
@[expose] public section
namespace RKCert.PortRank
open Polynomial RKCert.Paired RKCert.Paired.Terminal
variable {K:Type*} [Field K] [CharZero K]

theorem lobatto7_marked_factor_quartic (Z Q:K[X]) (u:K)
    (zm:Z.Monic) (zdiv:Z∣(X-1)*lobatto 7) (dz:Z.natDegree≤5)
    (hu:u≠0) (zu:Z.eval u=0) (dq:Q.natDegree≤4)
    (global : ∀k:Fin 4, (primitive ((X^k.val*Z)*Q)).eval 1=0)
    (local1 : (primitive (X*Q)).eval u=0) (local2 : (primitive (X^2*Q)).eval u=0) :
    Q=0 :=
  lobatto7_quartic_of_det port_det_integral Z Q u zm zdiv dz hu zu dq global local1 local2

/-- Five paid global moments, the direct shape supplied by the physical
DIRK reduction. The fifth one is not used. -/
theorem lobatto7_marked_factor_quartic_five (Z Q:K[X]) (u:K)
    (zm:Z.Monic) (zdiv:Z∣(X-1)*lobatto 7) (dz:Z.natDegree≤5)
    (hu:u≠0) (zu:Z.eval u=0) (dq:Q.natDegree≤4)
    (global : ∀k:Fin 5, (primitive ((X^k.val*Z)*Q)).eval 1=0)
    (local1 : (primitive (X*Q)).eval u=0) (local2 : (primitive (X^2*Q)).eval u=0) : Q=0 :=
  lobatto7_marked_factor_quartic Z Q u zm zdiv dz hu zu dq
    (fun k=>global ⟨k.val,by have:=k.isLt; omega⟩) local1 local2

end RKCert.PortRank
