module

public import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8HoleSixCompactProjection

/-- Three-by-three determinant, used for the clean-clock moment matrix. -/
def det3 {R : Type*} [CommRing R] (a b c d e f g h i : R) : R :=
  a * (e * i - f * h) - b * (d * i - f * g) + c * (d * h - e * g)

/-- Fraction-free Cramer recovery of the early physical-clock quadratic.
No determinant nonvanishing is needed for these coefficient identities. -/
theorem momentCramer {R : Type*} [CommRing R]
    (a b c d e f g h i A B C v w z : R)
    (h₀ : a*A+b*B+c*C=v) (h₁ : d*A+e*B+f*C=w) (h₂ : g*A+h*B+i*C=z) :
    det3 a b c d e f g h i * A = det3 v b c w e f z h i ∧
    det3 a b c d e f g h i * B = det3 a v c d w f g z i ∧
    det3 a b c d e f g h i * C = det3 a b v d e w g h z := by
  rw [← h₀, ← h₁, ← h₂]
  unfold det3
  constructor
  · ring
  · constructor <;> ring

/-- Transport the actual fourth root, fifth read, and zero-amplitude sixth
read to homogeneous Cramer coefficients. Neither U nor the Cramer
determinant is divided here. -/
theorem homogeneousActualReads {R : Type*} [CommRing R]
    (d A B C a b c q y U V D γ η L G M : R)
    (hA : d*A=a) (hB : d*B=b) (hC : d*C=c)
    (hroot : A+B*q+C*q^2=0)
    (heta : 8*η=B+C*(q+y))
    (hfive : U*η=γ^2*V)
    (hsix : (9-8*η)*γ^6*L+D*(G-32*η*M)=0) :
    a+b*q+c*q^2=0 ∧
    U*(b+c*(q+y))-8*γ^2*V*d=0 ∧
    (9*d-(b+c*(q+y)))*γ^6*L+D*(d*G-4*(b+c*(q+y))*M)=0 := by
  have hN : b+c*(q+y)=8*d*η := by
    linear_combination -hB-(q+y)*hC-d*heta
  refine ⟨?_, ?_, ?_⟩
  · linear_combination d*hroot-hA-q*hB-q^2*hC
  · linear_combination U*hN+8*d*hfive
  · linear_combination d*hsix-(γ^6*L+4*D*M)*hN

/-- Explicit quartic remainder on an actual quadratic root. This retains
every rank-drop case of the resulting linear equation. -/
theorem quarticRemainder {R : Type*} [CommRing R]
    (a b c q f₀ f₁ f₂ f₃ f₄ : R)
    (hq : a+b*q+c*q^2=0)
    (hf : f₀+f₁*q+f₂*q^2+f₃*q^3+f₄*q^4=0) :
    (c^3*f₀-c^2*a*f₂+c*a*b*f₃+(a^2*c-a*b^2)*f₄) +
      (c^3*f₁-c^2*b*f₂+c*(b^2-a*c)*f₃+(2*a*b*c-b^3)*f₄)*q=0 := by
  have h₂ : c*q^2 = -a-b*q := by linear_combination hq
  have h₃ : c^2*q^3 = a*b+(b^2-a*c)*q := by
    linear_combination c*q*h₂-b*h₂
  have h₄ : c^3*q^4 = a^2*c-a*b^2+(2*a*b*c-b^3)*q := by
    linear_combination c*q*h₃+(b^2-a*c)*h₂
  linear_combination c^3*hf-c^2*f₂*h₂-c*f₃*h₃-f₄*h₄

/-- The quadratic/linear projection without selecting a leading linear
pivot. If both linear coefficients vanish, the equation is still valid. -/
theorem quadraticLinearProjection {R : Type*} [CommRing R]
    (a b c l₀ l₁ q : R) (hq : a+b*q+c*q^2=0) (hl : l₀+l₁*q=0) :
    c*l₀^2 - b*l₀*l₁ + a*l₁^2=0 := by
  linear_combination l₁^2*hq-(b*l₁+c*(l₁*q-l₀))*hl

/-- The homogeneous two-linear projection, again with no pivot. -/
theorem linearProjection {R : Type*} [CommRing R]
    (l₀ l₁ m₀ m₁ q : R) (hl : l₀+l₁*q=0) (hm : m₀+m₁*q=0) :
    l₀*m₁-l₁*m₀=0 := by
  linear_combination m₁*hl-l₁*hm

end RKCert.ReviewedNative.SDIRK8HoleSixCompactProjection
