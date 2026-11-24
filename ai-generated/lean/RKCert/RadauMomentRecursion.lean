module
public import RKCert.RadauArithmetic77569

@[expose] public section

/-! # Denominator-cleared omitted-factor moments
The fixed 399 right Radau cases are replayed in a recurrence whose value and
homogeneity can be identified exactly over an arbitrary coefficient field. -/
namespace RKCert.FixedPolynomial.Radau77569

def factorMoment {R : Type*} [CommRing R] (u : R) : ℕ → List R → R
  | j, [] => ((420/(j+1):ℕ):R)*u^(j+1)
  | j, a::as => factorMoment u (j+1) as-a*factorMoment u j as

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3500000 in
theorem right_omitted_moment_rec :
    ∀ (u : Fin 7) (mask : Fin 128), mask.val.testBit u.val=false →
      (selected mask).length≤4 →
      factorMoment (rightRoots u) 1 ((selected mask).map rightRoots)≠0 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3500000 in
theorem mask_covers : ∀ bits : Fin 7→Bool,
    ∃ mask : Fin 128,∀ i : Fin 7, mask.val.testBit i.val=bits i := by decide

end RKCert.FixedPolynomial.Radau77569
