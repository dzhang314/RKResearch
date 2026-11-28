module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Polynomial.Degree.Domain
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8EightActiveSilentEighthFixedPeg

open Polynomial

/-- A nonzero constant read in a polynomial Bézout relation forces the
defect polynomial and its divided-difference transform to be coprime. -/
theorem coprimeOfConstantRead {K : Type*} [Field K]
    (H W D F : K[X]) (lam : K) (hlam : lam ≠ 0)
    (h : H*F-D*W=C lam) :
    IsCoprime H W := by
  refine ⟨C lam⁻¹ * F, -(C lam⁻¹ * D), ?_⟩
  calc
    (C lam⁻¹ * F)*H+(-(C lam⁻¹ * D))*W = C lam⁻¹ * (H*F-D*W) := by ring
    _ = 1 := by rw [h, ← C_mul, inv_mul_cancel₀ hlam, C_1]

/-- The lower-coefficient kernel of the known-peg reconstruction is
trivial. In the four-peg case the residual L is constant; in the fixed
top-three-row five-peg case it is affine. No unknown pivot or field
ordering is assumed. -/
theorem knownPegLowerKernel {K : Type*} [Field K]
    (E H W D D' F F' L : K[X]) (lam : K) (hlam : lam ≠ 0) (hD : D ≠ 0)
    (h : H*F-D*W=C lam) (h' : H*F'-D'*W=L)
    (hE : IsCoprime E H) (hED : E ∣ D) (hED' : E ∣ D')
    (hd : D'.natDegree < D.natDegree)
    (hdeg : D.natDegree + L.natDegree < (E*H).natDegree) :
    D' = 0 := by
  let Z := C lam * D' - L * D
  have hZW : H ∣ Z * W := by
    refine ⟨C lam * F' - L * F, ?_⟩
    dsimp [Z]
    calc
      (C lam*D'-L*D)*W =
          H*(C lam*F'-L*F) - (C lam*(H*F'-D'*W)-L*(H*F-D*W)) := by ring
      _ = H*(C lam*F'-L*F) := by rw [h',h]; ring
  have hHZ : H ∣ Z := (coprimeOfConstantRead H W D F lam hlam h).dvd_of_dvd_mul_right hZW
  have hEZ : E ∣ Z := by
    obtain ⟨d,ed⟩ := hED
    obtain ⟨d',ed'⟩ := hED'
    refine ⟨C lam*d'-L*d, ?_⟩
    dsimp [Z]
    rw [ed,ed']
    ring
  have hZdeg : Z.natDegree ≤ D.natDegree+L.natDegree := by
    dsimp [Z]
    refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · exact (natDegree_C_mul_le _ _).trans (Nat.le_trans (Nat.le_of_lt hd) (Nat.le_add_right ..))
    · simpa [Nat.add_comm] using (natDegree_mul_le (p:=L) (q:=D))
  have hZ0 : Z = 0 := by
    by_contra hz
    exact (not_lt_of_ge (natDegree_le_of_dvd (hE.mul_dvd hEZ hHZ) hz))
      (lt_of_le_of_lt hZdeg hdeg)
  have heq : C lam * D'=L*D := sub_eq_zero.mp hZ0
  have hL0 : L=0 := by
    by_contra hL
    have hh : D.natDegree ≤ (L*D).natDegree := by
      rw [natDegree_mul hL hD]
      exact Nat.le_add_left ..
    rw [← heq] at hh
    exact (not_lt_of_ge (hh.trans (natDegree_C_mul_le _ _))) hd
  rw [hL0,zero_mul] at heq
  exact (mul_eq_zero.mp heq).resolve_left (by simpa using hlam)

/-- The actual reverse three-read block on a silent eighth and two
ordinary successors has determinant `w b c (x-y)`. -/
theorem reverseSuccessorPivot {R : Type*} [CommRing R]
    (w b c y x z₁ z₂ : R) :
    (0 : R)*(b*y*z₂-c*x*z₁)-b*(0*z₂-c*x*w)+c*(0*z₁-b*y*w)
      = w*b*c*(x-y) := by ring

/-- Paid scalar values for the four trees in the order-seven
`bᵀ C² A h` read, with `h = (A-γI)(A c-c²/2)`. -/
theorem paidCubicReadCancellation (γ : ℚ) :
    1/168-1/2*(1/84)-γ*(1/36)+γ/2*(1/18)=0 := by ring

def minor3 {R : Type*} [CommRing R] (a b c d e f g h i : R) :=
  a*(e*i-f*h)-b*(d*i-f*g)+c*(d*h-e*g)

/-- Three genuine free strict taps cannot satisfy four affine equations
whose augmented determinant is nonzero. This is the exact cofactor
identity behind each paid local chronology rejection. -/
theorem paidAugmentedMinor {R : Type*} [CommRing R]
    (a₀ b₀ c₀ d₀ a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ a₃ b₃ c₃ d₃ x y z : R)
    (h₀ : a₀*x+b₀*y+c₀*z+d₀=0) (h₁ : a₁*x+b₁*y+c₁*z+d₁=0)
    (h₂ : a₂*x+b₂*y+c₂*z+d₂=0) (h₃ : a₃*x+b₃*y+c₃*z+d₃=0) :
    -d₀*minor3 a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃
    +d₁*minor3 a₀ b₀ c₀ a₂ b₂ c₂ a₃ b₃ c₃
    -d₂*minor3 a₀ b₀ c₀ a₁ b₁ c₁ a₃ b₃ c₃
    +d₃*minor3 a₀ b₀ c₀ a₁ b₁ c₁ a₂ b₂ c₂ = 0 := by
  linear_combination (norm := skip) -minor3 a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃*h₀
    +minor3 a₀ b₀ c₀ a₂ b₂ c₂ a₃ b₃ c₃*h₁
    -minor3 a₀ b₀ c₀ a₁ b₁ c₁ a₃ b₃ c₃*h₂
    +minor3 a₀ b₀ c₀ a₁ b₁ c₁ a₂ b₂ c₂*h₃
  unfold minor3
  ring

#print axioms coprimeOfConstantRead
#print axioms knownPegLowerKernel
#print axioms reverseSuccessorPivot
#print axioms paidCubicReadCancellation
#print axioms paidAugmentedMinor

end RKCert.ReviewedNative.SDIRK8EightActiveSilentEighthFixedPeg
