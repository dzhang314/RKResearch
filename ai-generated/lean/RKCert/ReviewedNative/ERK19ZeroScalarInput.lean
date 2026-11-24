module
public import RKCert.ReviewedNative.PositiveIntervalGrid19

@[expose] public section
namespace RKCert.ReviewedNative.ERK19ZeroScalar
open Polynomial RKCert.ReviewedNative.PositiveRule19
noncomputable section
variable {K : Type*} [Field K]

def opposedNodalProduct (z : Fin 4 → K) : K[X] :=
  (X-C (z 0))*(X-C (z 1))*(X-C (z 2))*(X-C (z 3))

variable [CharZero K]

structure OpposedQuinticWindows (P : K[X]) (z : Fin 4 → K) (e : ℕ) : Prop where
  degree : P.natDegree=5
  originBit : e≤1
  distinct : Function.Injective z
  active : ∀ i, z i≠0 ∧ z i≠1 ∧ P.eval (z i)≠0
  leftFirst : ∀ k : Fin 3, integral 0 (z 0) (X*P*X^k.val)=0
  leftSecond : ∀ k : Fin 2, integral 0 (z 1) (X*(X-C (z 0))*P*X^k.val)=0
  leftThird : integral 0 (z 2) (X*(X-C (z 0))*(X-C (z 1))*P)=0
  rightFirst : ∀ k : Fin 3, integral (z 3) 1 ((1-X)*P*X^k.val)=0
  rightSecond : ∀ k : Fin 2,
    integral (z 2) 1 ((1-X)*(X-C (z 3))*P*X^k.val)=0
  rightThird : integral (z 1) 1 ((1-X)*(X-C (z 3))*(X-C (z 2))*P)=0
  global : ∀ k : Fin (9-e),
    integral 0 1 ((1-X)*X^e*(P*opposedNodalProduct z)*X^k.val)=0

end
end RKCert.ReviewedNative.ERK19ZeroScalar
