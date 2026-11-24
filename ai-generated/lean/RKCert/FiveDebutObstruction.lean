module
public import RKCert.FiveDebutBridge
public import RKCert.FiveDebutScalar
@[expose] public section
namespace RKCert.FiveDebut
open RKCert.Paired RKCert.Paired.Clock RKCert.OneEscape
variable {K : Type*} [Field K] [CharZero K] {s p : ℕ} {A : Fin s→Fin s→K} {b : Vec K s}
variable {U : Submodule K (Vec K s)} {w : Vec K s}

/-- A grade-five single-head ordinary flag cannot persist through grade
seven in an order-ten-or-higher lower-triangular tableau. There is no
grade-eight hypothesis and no prior choice of physical knots or weights. -/
theorem no_grade5_head (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b p) (hp : 10≤p)
    (inv : U.map (diag (nodes A))≤U) (alg : MulClosed U) (inc : U≤zeroSpace A 5)
    (band : ∀ k≤2,zeroSpace A (5+k)=chain (diag (nodes A)) U w (1+k)) : False := by
  obtain ⟨z,W,h⟩:=original_refunded_five ha ho hp inv alg inc band
  obtain ⟨t,nt,amp⟩:=h.scale
  exact five_scalar_impossible z W h.injective h.nonzero t nt amp h.old h.first h.second

end RKCert.FiveDebut
