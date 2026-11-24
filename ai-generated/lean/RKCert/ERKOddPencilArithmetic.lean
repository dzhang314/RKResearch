module
public import RKCert.ERKOddZeroDispatch
public import RKCert.Dirk15ArithmeticSpecialize
public import RKCert.Dirk15ReplayInterface

@[expose] public section
/-! # Actual p17 pencil ports transport to the reusable exact norm pair -/
namespace RKCert.Paired.ERKOddHidden
open RKCert.FixedPolynomial RKCert.Paired.Signature RKCert.Endpoint Polynomial
variable {K:Type*} [Field K] [CharZero K]

omit [CharZero K] in
theorem oddPencil_is_fieldPencil (a:K):oddPencil a=fieldPencil K 7 a:=by
  norm_num [oddPencil,fieldPencil,fieldJacobi,integerJacobi]

theorem odd_pencil_impossible_of_pair
    (cert:Order15GoodPrimePair (nodeMomentNorm 7 5 1 0) (nodeMomentNorm 7 5 2 0) 210 210)
    (P:K[X])(a u:K)(B:OddPencilPorts P a u):False:=by
  have d:P∣fieldPencil K 7 a:=by rw [←oddPencil_is_fieldPencil];exact B.divides
  have e:(fieldPencil K 7 a).eval u=0:=by rw [←oddPencil_is_fieldPencil];exact B.root
  have a1:paidMoment ((1-X)^(0:ℕ)*P) u 1=0:=by
    simpa only [pow_zero,one_mul,paidMoment,pow_one,formalPrimitive_eq_treePrimitive] using B.first
  have a2:paidMoment ((1-X)^(0:ℕ)*P) u 2=0:=by
    simpa only [pow_zero,one_mul,paidMoment,formalPrimitive_eq_treePrimitive] using B.second
  have left:=(nodeMomentNorm_degree (n:=7) (k:=5) (by decide) (by decide) 1 0).trans (by decide:momentCap 7 5 0≤210)
  have right:=(nodeMomentNorm_degree (n:=7) (k:=5) (by decide) (by decide) 2 0).trans (by decide:momentCap 7 5 0≤210)
  exact cert.no_common left right u
    (nodeMomentNorm_zero (by decide) (by decide) B.nonzero B.degree e d B.omitted a1)
    (nodeMomentNorm_zero (by decide) (by decide) B.nonzero B.degree e d B.omitted a2)

end RKCert.Paired.ERKOddHidden

