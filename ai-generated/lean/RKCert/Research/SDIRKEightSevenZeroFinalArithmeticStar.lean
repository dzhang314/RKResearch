import Mathlib.Tactic.Ring.Basic

/-!
Scalar identities for the final arithmetic-front / live-star lower chart.
This module does not formalize the rooted flag or number-field projections.
-/

namespace RKResearch.Certified.SDIRKEightSevenZeroFinalArithmeticStar

variable {R : Type*} [CommRing R]

def H (u : R) : R := -2+u+4*u^2-u^3

def graphCube (p q : R) : R :=
  -2*p^3+q*p^2+4*q^2*p-q^3-(3*q-2*p)*p

theorem arithmetic_graph_cube {p u : R} (h : p*H u=3*u-2) :
    graphCube p (p*u)=0 := by
  calc
    _ = p^2*(p*H u-(3*u-2)) := by unfold graphCube H; ring1
    _ = _ := by rw [h,sub_self,mul_zero]

/-- No ordinary graph pivot is canceled. Its two Cramer numerators
satisfy this consequence even when the pivot is zero. -/
theorem division_free_arithmetic_cofactors
    {Δ p u Np Nq : R}
    (hp : Np=Δ*p) (hq : Nq=Δ*(p*u)) (h : p*H u=3*u-2) :
    -2*Np^3+Nq*Np^2+4*Nq^2*Np-Nq^3-(3*Nq-2*Np)*Np*Δ=0 := by
  calc
    _ = Δ^3*graphCube p (p*u) := by rw [hp,hq]; unfold graphCube; ring1
    _ = _ := by rw [arithmetic_graph_cube h,mul_zero]

def starF3 (y : R) : R := 2+6*y-3*y^2-y^3

/-- Convert the gap-free star equation to the reflected last-early
coordinate and factor the collision with the terminal clock. -/
theorem reflected_star_conversion (e n : R) :
    starF3 (2-e)-3-(2-e)-(1-e)*n*starF3 (2-e) =
      (e-1)*((e^3-9*e^2+18*e-6)*n+(e^2-8*e+11)) := by
  unfold starF3
  ring1

end RKResearch.Certified.SDIRKEightSevenZeroFinalArithmeticStar
