module

public import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8ReverseLiveAffineSharedQuinticHoleFiveStarSilentEight

/-- The three homogeneous signed rows for the true monic quadratic
are consequences of the paid coefficient identities, without a pivot. -/
theorem paidSignedQuadraticRows {R : Type*} [CommRing R]
    (r₀ r₁ m₀ m₁ m₂ m₃ m₄ ν₄ ν₅ e₄ H₃ H₄ : R)
    (h₁ : m₂+r₁*m₁+r₀*m₀=0)
    (h₂ : ν₄=H₄*(m₃+r₁*m₂+r₀*m₁))
    (h₃ : (e₄+r₁)*ν₄+ν₅-H₃*(m₃+r₁*m₂+r₀*m₁)-H₄*(m₄+r₁*m₃+r₀*m₂)=0) :
    m₀*r₀+m₁*r₁+m₂=0 ∧
      H₄*m₁*r₀+H₄*m₂*r₁+(H₄*m₃-ν₄)=0 ∧
      H₄^2*m₂*r₀+(H₄^2*m₃-H₄*ν₄)*r₁+
        (H₄^2*m₄-H₄*(e₄*ν₄+ν₅)+H₃*ν₄)=0 := by
  refine ⟨?_, ?_, ?_⟩
  · linear_combination h₁
  · linear_combination -h₂
  · linear_combination -H₄*h₃+H₃*h₂

/-- The true silent-eighth gap allows the paid terminal row to be written
with the three other known ordinary pegs represented by M(c), M(x).
No cancellation of u-2 or of an ordinarily silent amplitude occurs. -/
theorem trueSilentEighthTerminalRow {R : Type*} [CommRing R] [NoZeroDivisors R]
    (γ u c x hc hx Mc Mx Rc Rx φ : R)
    (hγ : γ ≠ 0) (hu : u ≠ 0) (hhx : hx ≠ 0)
    (hclock : c=x-γ*u) (hgap : (u-2)*hc=φ*hx)
    (hterm : hc*Mc*(c-x)*Rc=hx*Mx*(x-c)*Rx) :
    φ*Mc*Rc+(u-2)*Mx*Rx=0 := by
  have hZ : (γ*u*hx)*(φ*Mc*Rc+(u-2)*Mx*Rx)=0 := by
    rw [hclock] at hterm
    linear_combination -(u-2)*hterm-(γ*u*Mc*Rc)*hgap
  exact (mul_eq_zero.mp hZ).resolve_left (mul_ne_zero (mul_ne_zero hγ hu) hhx)

#print axioms paidSignedQuadraticRows
#print axioms trueSilentEighthTerminalRow

end RKCert.ReviewedNative.SDIRK8ReverseLiveAffineSharedQuinticHoleFiveStarSilentEight
