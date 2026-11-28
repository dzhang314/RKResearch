module

public import RKCert.ReviewedNative.DIRK12MidpointRealMomentInterval
public import RKCert.ReviewedNative.DIRKOrderTwelveMidpointStar
import Mathlib.Algebra.Polynomial.Coeff

@[expose] public section

/-! The recursive support moments really are the unit-interval integral
of the monic nodal products. This connects the directed enclosure to
the actual reviewed size-thirteen bush once scalar quadrature is paid. -/
namespace RKResearch.Certified.DIRK12MidpointRealInterval

open DirectedRatBox Polynomial
open RKResearch Graded FiniteRootedTree
open scoped Polynomial Matrix FiniteRootedTree

section Poly
variable {K : Type*} [Field K] [CharZero K]

noncomputable def integral : K[X] →ₗ[K] K :=
  Polynomial.lsum fun j => LinearMap.id.smulRight (((1 / ((j+1:Nat):ℚ)) : ℚ) : K)

theorem integral_pow (j : Nat) :
    integral ((X:K[X])^j) = ((1 / ((j+1:Nat):ℚ) : ℚ) : K) := by
  simp [integral,Polynomial.lsum_apply, X_pow_eq_monomial, LinearMap.smulRight_apply]

noncomputable def hull : List K → K[X]
  | [] => 1
  | r::rs => (X-C r)*hull rs

omit [CharZero K] in
theorem hull_monic (rs : List K) : (hull rs).Monic := by
  induction rs with
  | nil => exact monic_one
  | cons r rs ih => exact (monic_X_sub_C r).mul ih

omit [CharZero K] in
theorem hull_degree (rs : List K) : (hull rs).natDegree = rs.length := by
  induction rs with
  | nil => simp [hull]
  | cons r rs ih =>
    rw [hull, natDegree_mul (monic_X_sub_C r).ne_zero (hull_monic rs).ne_zero,
      natDegree_X_sub_C, ih]
    simp [Nat.add_comm]

omit [CharZero K] in
theorem hull_append (xs ys : List K) : hull (xs++ys) = hull xs * hull ys := by
  induction xs with
  | nil => simp [hull]
  | cons r rs ih => simp [hull,ih,mul_assoc]

theorem integral_hull (rs : List K) (j : Nat) :
    integral ((X:K[X])^j * hull rs) = moment rs j := by
  induction rs generalizing j with
  | nil => simpa [hull, moment] using integral_pow (K:=K) j
  | cons r rs ih =>
    have e : (X:K[X])^j * ((X-C r)*hull rs) =
        X^(j+1)*hull rs - r • (X^j*hull rs) := by
      rw [Polynomial.smul_eq_C_mul,pow_succ]
      ring
    rw [hull,e,map_sub,map_smul,smul_eq_mul,ih,ih,moment]

theorem integral_star : (13:K) * integral DIRK12MidpointStar.starPoly = 1 := by
  have e : (DIRK12MidpointStar.starPoly : K[X]) = (1:K) • ((X:K[X])^0) + (-12:K) • ((X:K[X])^1) + (66:K) • ((X:K[X])^2) + (-220:K) • ((X:K[X])^3) + (495:K) • ((X:K[X])^4) + (-792:K) • ((X:K[X])^5) + (924:K) • ((X:K[X])^6) + (-792:K) • ((X:K[X])^7) + (495:K) • ((X:K[X])^8) + (-220:K) • ((X:K[X])^9) + (66:K) • ((X:K[X])^10) + (-12:K) • ((X:K[X])^11) + (1:K) • ((X:K[X])^12) := by
    unfold DIRK12MidpointStar.starPoly
    rw [map_one]
    simp only [Polynomial.smul_eq_C_mul,map_ofNat,map_neg,map_one]
    ring
  rw [e]
  simp only [map_add,map_smul,smul_eq_mul,integral_pow,Nat.cast_add,Nat.cast_ofNat,
    Rat.cast_div,Rat.cast_add,Rat.cast_ofNat,Rat.cast_one,Rat.cast_natCast]
  norm_num

end Poly

section Real
variable {x f d v : ℝ}

noncomputable def supportHull (x f d v : ℝ) : ℝ[X] :=
  hull (fixed x f ++ [d,v,U (moments x f)])

theorem supportHull_monic (x f d v : ℝ) : (supportHull x f d v).Monic := hull_monic _

theorem supportHull_degree (x f d v : ℝ) : (supportHull x f d v).natDegree = 10 := by
  rw [supportHull,hull_degree]
  rfl

theorem exact_integral (hSum : d+v = S (moments x f)) (hProd : d*v = P (moments x f)) :
    -(13:ℝ) * integral (X^2*supportHull x f d v) = scalarExpression (moments x f) := by
  let n := moments x f
  let W := hull (fixed x f)
  have e : (X:ℝ[X])^2 * supportHull x f d v =
      X^5*W - (S n+U n) • (X^4*W) +
      (P n+S n*U n) • (X^3*W) - (P n*U n) • (X^2*W) := by
    unfold supportHull
    rw [hull_append]
    change (X:ℝ[X])^2*(W*((X-C d)*((X-C v)*((X-C (U n))*1)))) = _
    rw [← show d+v = S n from hSum, ← show d*v = P n from hProd]
    simp only [Polynomial.smul_eq_C_mul,map_add,map_mul]
    ring
  rw [e,map_sub,map_add,map_smul,map_smul,map_sub,map_smul]
  simp only [smul_eq_mul]
  change (-13:ℝ)*(integral (X^5*hull (fixed x f)) -
    (S n+U n)*integral (X^4*hull (fixed x f)) +
    (P n+S n*U n)*integral (X^3*hull (fixed x f)) -
    (P n*U n)*integral (X^2*hull (fixed x f))) = _
  rw [integral_hull,integral_hull,integral_hull,integral_hull]
  rfl

variable {ι : Type*} [Fintype ι]

theorem actual_star_bounded (A : Matrix ι ι ℝ) (b : ι → ℝ)
    (hx : Encloses xBox x) (hf : Encloses fBox f)
    (hSum : d+v = S (moments x f)) (hProd : d*v = P (moments x f))
    (weights : ∀ i, b i * (supportHull x f d v).eval (1-nodes A i) = 0)
    (low : ∀ Q : ℝ[X], Q.natDegree<12 → DIRK12MidpointStar.quadr A b Q = integral Q) :
    (starLo:ℝ) < (((bushyTree 13).factorial:Nat):ℝ) * (b ⬝ᵥ Φ (bushyTree 13) A)-1 ∧
      (((bushyTree 13).factorial:Nat):ℝ) * (b ⬝ᵥ Φ (bushyTree 13) A)-1 < (starHi:ℝ) := by
  rw [DIRK12MidpointStar.actual_star_defect A b _ (supportHull_monic _ _ _ _)
    (supportHull_degree _ _ _ _) integral low weights integral_star, exact_integral hSum hProd]
  exact midpoint_star_bounds hx hf

end Real
end RKResearch.Certified.DIRK12MidpointRealInterval

#print axioms RKResearch.Certified.DIRK12MidpointRealInterval.integral_hull
#print axioms RKResearch.Certified.DIRK12MidpointRealInterval.actual_star_bounded
