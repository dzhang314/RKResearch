import Mathlib.Tactic.Ring.Basic

namespace RKResearch.Certified.SDIRKEightDirtySevenQuadraticSddDssArithmeticReuse

variable {K : Type*} [CommRing K]

theorem ratio_pivot_identity (A B e s q M : K)
    (he : A+B*e=0) (hs : A+s*B=q*M) :
    B*(s-e)=q*M := by
  calc
    _ = (A+s*B)-(A+B*e) := by ring1
    _ = _ := by rw [hs,he,sub_zero]

theorem ratio_pivot_ne_zero [IsDomain K] (A B e s q M : K)
    (he : A+B*e=0) (hs : A+s*B=q*M) (hq : q≠0) (hm : M≠0) :
    B ≠ 0 := by
  intro hz
  have h := ratio_pivot_identity A B e s q M he hs
  rw [hz,zero_mul] at h
  exact (mul_ne_zero hq hm) h.symm

theorem cleared_paid_singleton (M q A F G mu : K)
    (hμ : M*q*mu=A) (h : F=mu*G) :
    M*q*F-A*G=0 := by
  rw [h]
  calc
    _ = (M*q*mu)*G-A*G := by ring1
    _ = 0 := by rw [hμ,sub_self]

end RKResearch.Certified.SDIRKEightDirtySevenQuadraticSddDssArithmeticReuse
