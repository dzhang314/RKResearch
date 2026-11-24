module

public import RKCert.ReviewedNative.ERKGradeEightQuarticPorts
public import RKCert.EndpointPhysical

@[expose] public section

/-! # The exact scalar obstruction for a physical 3+2 quartic

The only nonnative-name import is the tree-free endpoint rescaling and
its fixed coefficient lemma. No tableau/order conversion, matrix rank
claim, or newly generated arithmetic is part of this module. -/
namespace RKResearch.Certified.Graded
open Polynomial Module
open scoped Classical

variable {K : Type*} [Field K] [CharZero K] {P : K[X]} {u v : K}

/-- An actual nonzero observed quartic in characteristic zero forces an
exceptional ratio of its *two actual clocks*. No ordered field is needed
for this statement. -/
theorem Quartic3Plus2.exceptional_ratio (B : Quartic3Plus2 P u v) :
    15*(v/u)^2-24*(v/u)+10=0 := by
  classical
  let a := toFn 5 P
  have rep : ofFn 5 a=P := ofFn_comp_toFn_eq_id_of_natDegree_lt (by have := B.degree; omega)
  have mm (t : K) (k : ℕ) : (primitive (X^k*P)).eval t=RKCert.Endpoint.moment a t k := by
    rw [←rep]
    exact HeadContrast.primitive_monomial_moment a t k
  have first (k : Fin 3) : RKCert.Endpoint.moment a u (k.val+1)=0 := by
    have x := B.first (X^k.val) (by rw [natDegree_X_pow]; have := k.isLt; omega)
    have e : (X:K[X])^k.val*(X*P)=X^(k.val+1)*P := by rw [pow_succ]; ring
    rw [e,mm] at x
    exact x
  have second (k : Fin 2) :
      RKCert.Endpoint.moment a v (k.val+2)-u*RKCert.Endpoint.moment a v (k.val+1)=0 := by
    have x := B.second (X^k.val) (by rw [natDegree_X_pow]; have := k.isLt; omega)
    have e : (X:K[X])^k.val*(X*(X-C u)*P)=X^(k.val+2)*P-u • (X^(k.val+1)*P) := by
      rw [show k.val+2=(k.val+1)+1 by omega,pow_succ X (k.val+1),pow_succ X k.val,
        Polynomial.smul_eq_C_mul]
      ring
    rw [e,map_sub,map_smul,eval_sub,eval_smul,smul_eq_mul,mm,mm] at x
    exact x
  have paid : RKCert.EndpointPhysical.tests a u v 3 :=
    ⟨first,second 0,second 1⟩
  have scale := RKCert.EndpointPhysical.normalize B.first_ne paid
  rcases RKCert.Endpoint.quartic_three_two _ _ (div_ne_zero B.second_ne B.first_ne)
      (fun e => B.distinct ((div_eq_one_iff_eq B.first_ne).mp e)) scale with van|exceptional
  · have za := (RKCert.EndpointPhysical.rescale_eq_zero_iff a B.first_ne).mp van
    exact B.nonzero (by rw [←rep,za,map_zero]) |>.elim
  · exact exceptional

theorem Quartic3Plus2.impossible_ordered [LinearOrder K] [IsStrictOrderedRing K]
    (B : Quartic3Plus2 P u v) : False := by
  have e := B.exceptional_ratio
  nlinarith [sq_nonneg (5*(v/u)-4)]

end RKResearch.Certified.Graded
