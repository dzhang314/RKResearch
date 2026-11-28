module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.CharZero.Defs
import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8HoleSevenExceptionalTotalDrop

/-- The total row-six clock drop fixes the scaled continued quartic
correction, without selecting an actual sixth clock. -/
theorem scaledProfile {R : Type*} [CommRing R]
    (U V η lam d₁ d₂ s y v : R)
    (hη : η*U=V) (hlam : lam*U=d₂) (hV : d₂*(s+y)+d₁=V) :
    U*(η+lam*(v-y))=d₂*(s+v)+d₁ := by
  linear_combination hη+(v-y)*hlam-hV

/-- The sixth total drop cannot simultaneously lose the fifth pivot. -/
theorem necessaryUnits {R : Type*} [CommRing R] [NoZeroDivisors R]
    (U V η lam d₁ d₂ s y : R)
    (hη : η*U=V) (hlam : lam*U=d₂) (hV : d₂*(s+y)+d₁=V)
    (hd : d₂=0 → d₁≠0) (hl : lam≠0) : U≠0 ∧ d₂≠0 := by
  have hu : U≠0 := by
    intro hzero
    have hz : d₂=0 := by simpa [hzero] using hlam.symm
    have hv : V=0 := by simpa [hzero] using hη.symm
    exact hd hz (by simpa [hz,hv] using hV)
  exact ⟨hu, by rw [← hlam]; exact mul_ne_zero hl hu⟩

/-- On the rank-loss slope factor, the genuine fourth pivot requires the
specific fifth correction coefficient rather than a guessed amplitude. -/
theorem forcedEta {K : Type*} [Field K] [CharZero K]
    (D η : K) (hd : D≠0) (h : D*(8-64*η)=0) : 8*η=1 := by
  have h' := (mul_eq_zero.mp h).resolve_left hd
  linear_combination (-1/8:K)*h'

end RKCert.ReviewedNative.SDIRK8HoleSevenExceptionalTotalDrop
