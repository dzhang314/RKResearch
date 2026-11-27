module

public import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8GaussDoubleDependent

/-- Cancellation on the repeated active support leaves a virtual
read at the sole other clock carrying the reverse row. Neither
individually silent amplitude is replaced by that virtual value. -/
theorem twoClockVirtualBalance {R : Type*} [CommRing R]
    (r₀ r₁ a s₀ s₁ vR vA v₀ v₁ : R)
    (hr : r₀+r₁=0) (hs : a+s₀+s₁=0)
    (hv : r₀*vR+r₁*vR+a*vA+s₀*v₀+s₁*v₁=0) :
    s₀*(v₀-vA)+s₁*(v₁-vA)=0 := by
  linear_combination hv-vR*hr-vA*hs

/-- Two unpegged ordinary clocks imply a vanishing signed Hankel
determinant while its leading pivot is nonzero under the separate
mass and distinct-node guards. -/
theorem twoNodeSignedMoments {R : Type*} [CommRing R]
    (a b x y m₀ m₁ m₂ m₃ m₄ : R)
    (h₀ : m₀=a+b) (h₁ : m₁=a*x+b*y) (h₂ : m₂=a*x^2+b*y^2)
    (h₃ : m₃=a*x^3+b*y^3) (h₄ : m₄=a*x^4+b*y^4) :
    (m₀*m₂*m₄+2*m₁*m₂*m₃-m₀*m₃^2-m₁^2*m₄-m₂^3=0) ∧
      (m₀*m₂-m₁^2=a*b*(x-y)^2) := by
  rw [h₀,h₁,h₂,h₃,h₄]
  constructor <;> ring

/-- The profile coefficient can be eliminated without division by the
ordinary value or the transported Legendre read. In particular this
identity does not discard the separate vanishing profile locus. -/
theorem ordinaryFrontCross {K : Type*} [Field K]
    (δ q y u v ρ : K)
    (hd : δ ≠ 0) (h₄ : δ*u=ρ*(δ*q)) (h₅ : v=ρ*y) :
    y*u-v*q=0 := by
  have h : (y*u-v*q)*δ=0 := by
    linear_combination y*h₄-q*δ*h₅
  exact (mul_eq_zero.mp h).resolve_right hd

/-- With vanishing reverse quadratic factor, a nonzero reverse row
combination must detect one of the two literal terminal clocks. -/
theorem terminalSupportChoice {K : Type*} [Field K]
    (r x c α β w n b₁ b₂ h₁ h₂ : K)
    (hw : w ≠ 0) (hn : n ≠ 0)
    (hdet : α ≠ 0 ∨ β ≠ 0)
    (hₓ : b₁*h₁=α*w) (hc : b₂*h₂=β*n)
    (hs₁ : h₁ ≠ 0 → r=x) (hs₂ : h₂ ≠ 0 → r=c) :
    r=x ∨ r=c := by
  rcases hdet with h | h
  · left
    apply hs₁
    intro hzero
    rw [hzero,mul_zero] at hₓ
    exact mul_ne_zero h hw hₓ.symm
  · right
    apply hs₂
    intro hzero
    rw [hzero,mul_zero] at hc
    exact mul_ne_zero h hn hc.symm

#print axioms twoClockVirtualBalance
#print axioms twoNodeSignedMoments
#print axioms ordinaryFrontCross
#print axioms terminalSupportChoice

end RKCert.ReviewedNative.SDIRK8GaussDoubleDependent
