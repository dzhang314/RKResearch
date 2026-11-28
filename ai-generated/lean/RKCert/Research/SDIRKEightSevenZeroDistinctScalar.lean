import Mathlib.Tactic.Ring.Basic

/-!
Scalar identities for the seven-distinct-zero pure two-clock chart. The
hypotheses are the extracted causal scalar gates, not a rooted-tableau predicate.
-/

namespace RKResearch.Certified.SDIRKEightSevenZeroDistinctScalar

variable {R : Type*} [CommRing R]

/-- Eliminate the common second-row Legendre value without any division. -/
theorem shared_line_cancel {l r s₀ s₁ f₀ f₁ : R}
    (h₀ : l*f₀ + r*s₀ = 0) (h₁ : l*f₁ + r*s₁ = 0) :
    l*(s₁*f₀-s₀*f₁) = 0 := by
  calc
    _ = s₁*(l*f₀+r*s₀)-s₀*(l*f₁+r*s₁) := by ring1
    _ = _ := by rw [h₀,h₁]; ring1

/-- Star reflection: equality of the two cardinal numerators removes the
squared displacement from the ordinary nodal condition. -/
theorem star_recovery_cancel {m₀ m₂ v : R}
    (h₀ : m₀ = 0) (h₂ : m₂ - v*m₀ = 0) : m₂ = 0 := by
  simpa only [h₀, mul_zero, sub_zero] using h₂

def rearK (v : R) : R := 1+2*v-v^2
def rearH (v : R) : R := v^3-4*v^2-v+2
def rearQ (v : R) : R := 4*v^3-12*v^2+3*v+2

def rearSextic (v : R) : R :=
  8*v^6-44*v^5+22*v^4+97*v^3-55*v^2-13*v+6

/-- Six times the primitive of the cleared arithmetic rear quadratic.
Its three rear values are H, H·κ and −κ·Q. -/
def arithPrimitive6 (v y : R) : R :=
  let h := rearH v
  let j := 3*v-2
  let p₀ := -2*h+2*j*(1+v)
  let p₁ := 4*h-2*j*(2+v)
  let p₂ := -h+2*j
  6*p₀*y+3*p₁*y^2+2*p₂*y^3

theorem arithmetic_rear_sextic_identity (v : R) :
    rearH v * arithPrimitive6 v (1+2*v) +
      rearQ v * (2*arithPrimitive6 v (1+v)-rearK v*arithPrimitive6 v 1) =
      (-4)*rearH v*rearSextic v := by
  unfold arithPrimitive6 rearH rearQ rearK rearSextic
  ring1

theorem arithmetic_rear_sextic [IsDomain R] {v : R}
    (h₄ : (4:R) ≠ 0) (hκ : rearK v ≠ 0) (hH : rearH v ≠ 0)
    {κ₃ : R} (h₃ : rearH v * κ₃ = -(rearK v * rearQ v))
    (hAff : rearK v * arithPrimitive6 v (1+2*v) =
      κ₃ * (2*arithPrimitive6 v (1+v)-rearK v*arithPrimitive6 v 1)) :
    rearSextic v = 0 := by
  let aux := 2*arithPrimitive6 v (1+v)-rearK v*arithPrimitive6 v 1
  have hh : rearK v * (rearH v * arithPrimitive6 v (1+2*v)+rearQ v*aux) = 0 := by
    calc
      _ = rearH v*(rearK v*arithPrimitive6 v (1+2*v))+
        (rearK v*rearQ v)*aux := by ring1
      _ = rearH v*(κ₃*aux)+(rearK v*rearQ v)*aux := by rw [hAff]
      _ = (rearH v*κ₃)*aux+(rearK v*rearQ v)*aux := by ring1
      _ = _ := by rw [h₃]; ring1
  have hz : (-4:R)*rearH v*rearSextic v = 0 := by
    rw [← arithmetic_rear_sextic_identity]
    exact (mul_eq_zero.mp hh).resolve_left hκ
  exact (mul_eq_zero.mp hz).resolve_left (mul_ne_zero (neg_ne_zero.mpr h₄) hH)

end RKResearch.Certified.SDIRKEightSevenZeroDistinctScalar
