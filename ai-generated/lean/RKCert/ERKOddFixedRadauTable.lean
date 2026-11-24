module
public import RKCert.ERKOddFixedRadau
@[expose] public section
namespace RKCert.RadauEight.FirstMoment
open Polynomial RKCert.FixedFactor RKCert.Paired
set_option maxRecDepth 50000
set_option maxHeartbeats 0
/-- 3,056 exact nonzero first primitives on the actual fixed grid. -/
theorem verified_radau8_first_moments:checked 420 5 gridp knots=true:=by decide +kernel
variable {K:Type*} [Field K] [CharZero K]
theorem radau8_first_moment {P:K[X]} {u:K}
    (div:P∣(RKCert.Paired.FiniteMidpoint.odd8:K[X])) (deg:P.natDegree≤5)
    (un:u≠0)(hit:(RKCert.Paired.FiniteMidpoint.odd8:K[X]).eval u=0):
    (primitive (X*P)).eval u≠0:=native_of_check verified_radau8_first_moments div deg un hit
end RKCert.RadauEight.FirstMoment
