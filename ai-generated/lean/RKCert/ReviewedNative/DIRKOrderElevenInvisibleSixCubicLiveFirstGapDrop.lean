module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.CharP.Defs
import Mathlib.Tactic.LinearCombination

@[expose] public section

/-! # Shared old primitive coefficients and the live first-gap Phi pivot -/
namespace RKResearch.Certified.Graded.OrderElevenInvisibleSixCubicLiveFirstGapDrop

/-- The two affine primitive comparisons have the same old
coefficient denominators. Eliminating their multipliers needs
neither a middle nor an intercept division. -/
theorem shared_primitive_projection {K : Type*} [Field K]
    (d₁ d₂ δ η r s c₀ c₁ c₂ : K) (hδ : δ≠0) (h2 : (2:K)≠0)
    (hr : 12*δ*d₁=r) (hs : 4*δ*d₂=s)
    (h₁ : 60*η*d₁=8*c₁-3*r*c₂) (h₂ : 20*η*d₂=6*c₀-s*c₂) :
    4*c₁*s=r*(3*c₀+c₂*s) := by
  have h₁' : 5*η*r=δ*(8*c₁-3*r*c₂) := by
    linear_combination δ*h₁-5*η*hr
  have h₂' : 5*η*s=δ*(6*c₀-s*c₂) := by
    linear_combination δ*h₂-5*η*hs
  have hh : (2*δ)*(4*c₁*s-r*(3*c₀+c₂*s))=0 := by
    linear_combination r*h₂'-s*h₁'
  exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (mul_ne_zero h2 hδ))

/-- The fourth-stage weighted reads yield the undivided Phi
relation once the common old coefficient ratio is used. -/
theorem fourth_phi_relation {K : Type*} [CommRing K] (δ r t V : K)
    (hr : r=12*δ*(t-r)) (hv : (1-4*δ)*V=2*δ*t) :
    r*(t+8*V)=6*V*t := by
  linear_combination (2*V+t)*hr-6*(t-r)*hv

/-- Phi cannot vanish: the right-hand side would have a
nonzero factor (t=-8V). -/
theorem phi_live {K : Type*} [Field K] [CharZero K] (r t V : K) (hv : V≠0)
    (h : r*(t+8*V)=6*V*t) : t+8*V ≠ 0 := by
  intro hz
  have h8 : (8:K)≠0 := Nat.cast_ne_zero.mpr (by decide : (8:ℕ)≠0)
  have h6 : (6:K)≠0 := Nat.cast_ne_zero.mpr (by decide : (6:ℕ)≠0)
  have ht : t≠0 := by
    intro h₀
    have hb : (8:K)*V=0 := by simpa [h₀] using hz
    exact (mul_ne_zero h8 hv) hb
  have hh : 6*V*t=0 := by simpa [hz] using h.symm
  exact (mul_ne_zero (mul_ne_zero h6 hv) ht) hh

end RKResearch.Certified.Graded.OrderElevenInvisibleSixCubicLiveFirstGapDrop
