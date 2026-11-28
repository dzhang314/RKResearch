module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.CharP.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

@[expose] public section

/-! # Live cubic and monomial reverse-fit scalar gates -/
namespace RKResearch.Certified.Graded.OrderElevenInvisibleSixCubicLiveMonomial

section Ring
variable {K : Type*} [CommRing K]

def det₃ (a b c d e f g h i : K) : K :=
  a*(e*i-f*h)-b*(d*i-f*g)+c*(d*h-e*g)

/-- Exact affinity determinant for a monic quadratic fit, with the
third coordinate column scaled by twelve. -/
theorem affinity_det (r s c₀ c₁ c₂ : K) :
    det₃ s (-c₀) (-3*c₀)
      r (s-c₁) (6*s-3*c₁)
      1 (r-c₂) (4*r-3*c₂) =
      -2*s^2*r+3*s^2*c₂-s*r*c₁-3*s*c₀+r^2*c₀ := by
  unfold det₃
  ring

end Ring

section Field
variable {K : Type*} [Field K]

/-- A linear reverse fit cannot have two nonzero terms. The
identities have been cleared of small denominators. -/
theorem linear_fit_monomial (x y a b : K)
    (h₀ : a*x=0) (h₁ : 2*(a*y+b*x)=x) (h₂ : 3*b*y=y) :
    x=0 ∨ y=0 := by
  by_cases hx : x=0
  · exact Or.inl hx
  · by_cases hy : y=0
    · exact Or.inr hy
    · have za : a=0 := (mul_eq_zero.mp h₀).resolve_right hx
      have hb : (2*b-1)*x=0 := by
        rw [za,zero_mul,zero_add] at h₁
        linear_combination h₁
      have hc : (3*b-1)*y=0 := by linear_combination h₂
      have hb' := (mul_eq_zero.mp hb).resolve_right hx
      have hc' := (mul_eq_zero.mp hc).resolve_right hy
      have bad : (1:K)=0 := by linear_combination 2*hc'-3*hb'
      exact (one_ne_zero bad).elim

/-- Two different actual primitive orders at the same clean
site force the pure-power fit to continue to that site. -/
theorem two_primitive_match (V p q d e : K) (hV : V≠0) (hpq : p≠q)
    (hp : e*(V*p-d)=0) (hq : e*(V*q-d)=0) : e=0 := by
  have h : e*(V*(p-q))=0 := by linear_combination hp-hq
  exact (mul_eq_zero.mp h).resolve_right (mul_ne_zero hV (sub_ne_zero.mpr hpq))

variable [CharZero K]

/-- The cubic case uses the additional paid quartic primitive.
The two individual coefficients may vanish. -/
theorem cubic_quartic_pair (V q c₀ c₁ c₂ : K) (hV : V≠0)
    (h₁ : (3*V^2+3*c₂*V+2*c₁)*q= -3*c₀*V^2-c₁*V^3)
    (h₂ : (-18*V^2-15*c₂*V-10*c₁)*q= -3*V^5+5*c₁*V^3+15*c₀*V^2) :
    q=V^3 := by
  have h : (-3 : K)*V^2*(q-V^3)=0 := by linear_combination h₂+5*h₁
  have hn : (-3 : K) ≠ 0 := neg_ne_zero.mpr (by exact_mod_cast (show (3:ℕ) ≠ 0 by decide))
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left (mul_ne_zero hn (pow_ne_zero 2 hV)))

end Field

end RKResearch.Certified.Graded.OrderElevenInvisibleSixCubicLiveMonomial
