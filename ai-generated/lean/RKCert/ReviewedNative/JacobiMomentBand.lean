module

public import RKCert.ReviewedNative.JacobiMomentPorts
import RKCert.EndpointJacobiTwoBand
import RKCert.Dirk15IntegerJacobi

@[expose] public section

/-! # Consecutive unit moments cut out the top two Jacobi directions

This is a degree-parametric consumer of the existing algebraic Jacobi basis.
It uses no tabulated row reductions, determinant, specific RK order or norm pair.
The source of the old Jacobi lemmas also imports geometry; their use here is
exclusively polynomial. -/
namespace RKCert.ReviewedNative.JacobiMoments
open Polynomial RKCert.Endpoint RKCert.Paired RKCert.FixedPolynomial

variable {K : Type*} [Field K] [CharZero K] {D : K[X]} {r : ℕ}

private theorem quiet_of_differences (B : MomentDifferences D r)
    (Q : K[X]) (qd : Q.natDegree ≤ r) : jacobiPair D Q = 0 := by
  let L : K[X] →ₗ[K] K := unitIntegral.comp (LinearMap.mulLeft K ((X*(1-X))*D))
  have mono (k : Fin (r+1)) : L (X^k.val) = 0 := by
    change unitIntegral (((X*(1-X))*D)*X^k.val) = 0
    rw [show ((X*(1-X))*D)*X^k.val =
        X^k.val*(X*D) - X^(k.val+1)*(X*D) by rw [pow_succ]; ring,
      map_sub, unitIntegral_apply, unitIntegral_apply]
    exact sub_eq_zero.mpr (B k)
  change L Q = 0
  conv_lhs => rw [Q.as_sum_support, map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  have d := (le_natDegree_of_mem_supp _ hi).trans qd
  rw [← C_mul_X_pow_eq_monomial, ← smul_eq_C_mul, map_smul, mono ⟨i,by omega⟩, smul_zero]

/-- r+1 differences on a polynomial of degree at most r+2 put it in the
span of the signed slopes of Legendre degrees r+3 and r+2. The two
coefficients can be zero; their vanishing is not decided from geometry. -/
theorem signedSlope_band (deg : D.natDegree ≤ r+2) (B : MomentDifferences D r) :
    ∃ v w : K, D = C v*signedSlope K (r+3) + C w*signedSlope K (r+2) := by
  obtain ⟨v,w,e⟩ := jacobiTwo_top_two (d:=r+2) (by omega) deg (by
    intro Q qd; exact quiet_of_differences B Q (by omega))
  rw [show r+2-1=r+1 by omega] at e
  obtain ⟨c,cn,hc⟩ := fieldJacobi_scale (K:=K) (r+2)
  obtain ⟨d,dn,hd⟩ := fieldJacobi_scale (K:=K) (r+1)
  have eqJ (k : ℕ) : signedSlope K (k+1) = fieldJacobi K k := by
    simp [signedSlope,fieldJacobi,integerJacobi]
  refine ⟨v/c,w/d,?_⟩
  rw [eqJ (r+2),eqJ (r+1),hc,hd,←mul_assoc,←mul_assoc,←map_mul,←map_mul,
    div_mul_cancel₀ _ cn,div_mul_cancel₀ _ dn]
  exact e

end RKCert.ReviewedNative.JacobiMoments
