module
public import RKCert.ReviewedNative.DIRK12MidpointRealStarBridge
public import RKCert.ReviewedNative.DIRK12MidpointMomentTransfers
public import RKCert.ReviewedNative.PaidNodalQuadrature
import Mathlib.Tactic.FieldSimp

@[expose] public section

/-! The two exact algebraic moment relations are sufficient for the
actual ten-site interpolation quadrature through degree eleven.
The relations themselves are left as explicit premises. -/
namespace RKResearch.Certified.DIRK12MidpointRealInterval

open DirectedRatBox Polynomial
open scoped Polynomial
open DIRK12MidpointMomentTransfers (k0 k1 k2 k3 rel3 rel4)

theorem integral_support (x f d v : ℝ)
    (hSum : d+v = S (moments x f)) (hProd : d*v = P (moments x f)) (j : Nat) :
    integral (X^j*supportHull x f d v) =
      moment (fixed x f) (j+3) - (S (moments x f)+U (moments x f))*moment (fixed x f) (j+2) +
      (P (moments x f)+S (moments x f)*U (moments x f))*moment (fixed x f) (j+1) -
      P (moments x f)*U (moments x f)*moment (fixed x f) j := by
  let n := moments x f
  let W := hull (fixed x f)
  have e : (X:ℝ[X])^j * supportHull x f d v =
      X^(j+3)*W - (S n+U n) • (X^(j+2)*W) +
      (P n+S n*U n) • (X^(j+1)*W) - (P n*U n) • (X^j*W) := by
    unfold supportHull
    rw [hull_append]
    change (X:ℝ[X])^j*(W*((X-C d)*((X-C v)*((X-C (U n))*1)))) = _
    rw [← show d+v = S n from hSum, ← show d*v = P n from hProd]
    simp only [Polynomial.smul_eq_C_mul,map_add,map_mul,pow_add]
    ring
  rw [e,map_sub,map_add,map_smul,map_smul,map_sub,map_smul]
  simp only [smul_eq_mul]
  change integral (X^(j+3)*hull (fixed x f)) -
    (S n+U n)*integral (X^(j+2)*hull (fixed x f)) +
    (P n+S n*U n)*integral (X^(j+1)*hull (fixed x f)) -
    (P n*U n)*integral (X^j*hull (fixed x f)) = _
  rw [integral_hull,integral_hull,integral_hull,integral_hull]

theorem scaled_support_coefficient {K : Type*} [Field K] (n : Fin 6 → K)
    (ha : aa n ≠ 0) (hb : bb n ≠ 0) (hc : cc n ≠ 0) (w0 w1 w2 w3 : K) :
    den n*(w3-(S n+U n)*w2+(P n+S n*U n)*w1-P n*U n*w0) =
      k3 (lab n) (lbb n) (ee n)*w3 + k2 (lab n) (lbb n) (ee n)*w2 +
      k1 (lab n) (lbb n) (ee n)*w1 + k0 (lab n) (lbb n) (ee n)*w0 := by
  unfold den S P U k3 k2 k1 k0
  rw [show DIRK12MidpointMomentTransfers.A (lab n) (lbb n) = aa n from rfl,
    show DIRK12MidpointMomentTransfers.B (lab n) (lbb n) = bb n from rfl,
    show DIRK12MidpointMomentTransfers.C (lab n) (lbb n) = cc n from rfl]
  field_simp [ha,hb,hc]
  ring

theorem two_support_moments (x f d v : ℝ)
    (hx : Encloses xBox x) (hf : Encloses fBox f)
    (hSum : d+v = S (moments x f)) (hProd : d*v = P (moments x f))
    (h3 : rel3 (moments x f 0) (moments x f 1) (moments x f 2) (moments x f 3)=0)
    (h4 : rel4 (moments x f 0) (moments x f 1) (moments x f 2)
      (moments x f 3) (moments x f 4)=0) :
    integral (supportHull x f d v)=0 ∧ integral (X*supportHull x f d v)=0 := by
  let n := moments x f
  have box := moments_enclosed hx hf
  have dp := (supportD_pos box).ne'
  obtain ⟨hA,hB,hC,_,_⟩ := all_pivots box
  constructor
  · have e := integral_support x f d v hSum hProd 0
    change integral (X^0*supportHull x f d v) =
      n 3 - (S n+U n)*n 2 + (P n+S n*U n)*n 1 - P n*U n*n 0 at e
    rw [pow_zero,one_mul] at e
    have t := scaled_support_coefficient n hA.ne' hB.ne' hC.ne' (n 0) (n 1) (n 2) (n 3)
    rw [← e] at t
    change den n*integral (supportHull x f d v) =
      _ at t
    unfold lab lbb ee at t
    rw [DIRK12MidpointMomentTransfers.paid_hull0,h3,mul_zero] at t
    exact (mul_eq_zero.mp t).resolve_left dp
  · have e := integral_support x f d v hSum hProd 1
    change integral (X^1*supportHull x f d v) =
      n 4 - (S n+U n)*n 3 + (P n+S n*U n)*n 2 - P n*U n*n 1 at e
    rw [pow_one] at e
    have t := scaled_support_coefficient n hA.ne' hB.ne' hC.ne' (n 1) (n 2) (n 3) (n 4)
    rw [← e] at t
    unfold lab lbb ee at t
    rw [DIRK12MidpointMomentTransfers.paid_hull1,h3,h4,mul_zero,mul_zero,add_zero] at t
    exact (mul_eq_zero.mp t).resolve_left dp

theorem scalar_quadrature_of_two_relations (x f d v : ℝ)
    (hx : Encloses xBox x) (hf : Encloses fBox f)
    (hSum : d+v = S (moments x f)) (hProd : d*v = P (moments x f))
    (h3 : rel3 (moments x f 0) (moments x f 1) (moments x f 2) (moments x f 3)=0)
    (h4 : rel4 (moments x f 0) (moments x f 1) (moments x f 2)
      (moments x f 3) (moments x f 4)=0)
    (sites : Fin 10 → ℝ) (distinct : Function.Injective sites)
    (hull_eq : Lagrange.nodal Finset.univ sites = supportHull x f d v)
    (q : ℝ[X]) (hq : q.natDegree<12) :
    PaidNodalQuadrature.quadr Finset.univ sites integral q = integral q := by
  obtain ⟨h0,h1⟩ := two_support_moments x f d v hx hf hSum hProd h3 h4
  have h0p : integral (Lagrange.nodal Finset.univ sites) = 0 := by rwa [hull_eq]
  have h1p : integral (X*Lagrange.nodal Finset.univ sites) = 0 := by rwa [hull_eq]
  exact PaidNodalQuadrature.exact_two_more Finset.univ sites integral Finset.univ_nonempty
    distinct.injOn h0p h1p q (by simpa using hq)

end RKResearch.Certified.DIRK12MidpointRealInterval

#print axioms RKResearch.Certified.DIRK12MidpointRealInterval.scalar_quadrature_of_two_relations
