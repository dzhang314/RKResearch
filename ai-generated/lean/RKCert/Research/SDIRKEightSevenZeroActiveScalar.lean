import Mathlib.Tactic.Ring.Basic

/-!
Scalar gates for the active canceled pair, seven physical zero chart.
The saturation and actual chronological ingress are supplied by the paper
proof; these are not rooted-tableau theorems.
-/

namespace RKResearch.Certified.SDIRKEightSevenZeroActiveScalar

variable {R : Type*} [CommRing R]

/-- Six times the primitive of (T-a)(T-b). -/
def prim2 (a b x : R) : R := x*(2*x^2-3*(a+b)*x+6*a*b)

/-- Twelve times the primitive of T(T-a)(T-b). -/
def prim3 (a b x : R) : R := x^2*(3*x^2-4*(a+b)*x+6*a*b)

theorem forward_primitive_pivot (a b : R) :
    prim2 a b a * prim3 a b b - prim2 a b b * prim3 a b a =
      3*a^2*b^2*(a-b)^3 := by
  unfold prim2 prim3
  ring1

/-- The ordinary nodal relation is linear in the last unassigned clock.
The same cleared cardinal numerator for the other clock is independent of r. -/
theorem ordinary_pencil {m₀ m₁ m₂ r e : R}
    (h : m₂-(r+e)*m₁+r*e*m₀ = 0) :
    (r*m₀-m₁)*e = r*m₁-m₂ ∧
    (r*m₀-m₁)*m₁-(r*m₁-m₂)*m₀ = m₀*m₂-m₁^2 := by
  constructor
  · calc
      _ = (r*m₁-m₂)+(m₂-(r+e)*m₁+r*e*m₀) := by ring1
      _ = _ := by rw [h, add_zero]
  · ring1

def tap2 (v w : R) : R := 2*w*v+1+2*w-w^2

theorem arith_rear_primitive (v : R) :
    tap2 v (2*v)*prim2 (1+2*v) (1+v) (1+v) -
      2*v^2*prim2 (1+2*v) (1+v) (1+2*v) =
      -(v^2-2*v-1)*(8*v^3+20*v^2+13*v+2) := by
  unfold tap2 prim2
  ring1

theorem star_rear_primitive (v : R) :
    tap2 v (2-v)*prim2 (1+(2-v)) (1+v) (1+v) -
      2*v^2*prim2 (1+(2-v)) (1+v) (1+(2-v)) =
      4*(v^2-2*v-1)*(v^3+8*v^2-11*v-2) := by
  unfold tap2 prim2
  ring1

/-- Clear the affine annihilator and the literal tap ratio in the third rear
read. Neither the prospective third weight nor its cardinal value is inverted. -/
theorem reverse_third_clear [IsDomain R]
    {Bs Bt Br pr v r s t α β μ Jt Fr : R}
    (hBt : Bt ≠ 0)
    (hTap : v*Bt*(α+β*s) = pr*Bs*(α+β*t))
    (ht : -(Bt*Jt) = μ*(α+β*t))
    (hr : Br*Fr = μ*(α+β*r)) :
    v*(s-t)*Br*Fr +
      Jt*(v*(s-t)*Bt+(r-t)*(pr*Bs-v*Bt)) = 0 := by
  have cleared :
      Bt * (v*(s-t)*Br*Fr +
        Jt*(v*(s-t)*Bt+(r-t)*(pr*Bs-v*Bt))) = 0 := by
    calc
      _ = (v*Bt)*(s-t)*(Br*Fr) -
            (-(Bt*Jt))*(v*(s-t)*Bt+(r-t)*(pr*Bs-v*Bt)) := by ring1
      _ = (v*Bt)*(s-t)*(μ*(α+β*r)) -
            (μ*(α+β*t))*(v*(s-t)*Bt+(r-t)*(pr*Bs-v*Bt)) := by rw [ht, hr]
      _ = μ*(r-t)*(v*Bt*(α+β*s)-pr*Bs*(α+β*t)) := by ring1
      _ = _ := by rw [hTap, sub_self, mul_zero]
  exact (mul_eq_zero.mp cleared).resolve_left hBt

end RKResearch.Certified.SDIRKEightSevenZeroActiveScalar
