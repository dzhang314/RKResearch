import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixAlphaTwoCompletion

theorem counts {beta gamma : Nat} (hs : 2 + beta + gamma = 6) (hg : 3 ≤ gamma) :
    (beta = 0 ∧ gamma = 4) ∨ (beta = 1 ∧ gamma = 3) := by omega

section Ring

variable {K : Type*} [CommRing K]

/-- No division by the fourth reverse head, first quartic, or an actual
ghost clock is needed to extend the old affine relation to V. -/
theorem genuine_fourth_read {v l0 l1 j θ a d k W Q : K}
    (h₀ : l0 = k*W) (h₁ : l1-v*l0 = k*Q+θ*j)
    (hq : Q = W*(a+d*v)) :
    l1 = θ*j + (v+a)*l0 + d*v*l0 := by
  rw [h₀] at h₁ ⊢
  rw [hq] at h₁
  linear_combination h₁

def det3 (j0 j1 j2 l0 l1 l2 m0 m1 m2 : K) : K :=
  j0*(l1*m2-l2*m1) - j1*(l0*m2-l2*m0) + j2*(l0*m1-l1*m0)

def det4cols (j l m n : Fin 4 → K) : K :=
  -(n 0)*det3 (j 1) (j 2) (j 3) (l 1) (l 2) (l 3) (m 1) (m 2) (m 3)
   + (n 1)*det3 (j 0) (j 2) (j 3) (l 0) (l 2) (l 3) (m 0) (m 2) (m 3)
   - (n 2)*det3 (j 0) (j 1) (j 3) (l 0) (l 1) (l 3) (m 0) (m 1) (m 3)
   + (n 3)*det3 (j 0) (j 1) (j 2) (l 0) (l 1) (l 2) (m 0) (m 1) (m 2)

/-- The four ordinary sample rows, with their actual common affine
coefficients. This uses only dependence of columns, not a Vandermonde
division. -/
theorem ordinary_det_zero {j l m n : Fin 4 → K} {θ a d : K}
    (h : ∀ i, n i = θ*j i+a*l i+d*m i) :
    det4cols j l m n = 0 := by
  unfold det4cols
  rw [h 0,h 1,h 2,h 3]
  unfold det3
  ring

end Ring

variable {K : Type*} [Field K]

/-- Clear the actual adjacent fifth-clean commutator and first forward
clean primitive. The only cancelled factor here is the known live
ordinary P0(B); no diagonal is cancelled. -/
theorem adjacent_signal {delta b u E d J S P : K}
    (hp : P ≠ 0) (hS : S*u = P*E)
    (hJ : d*b*u=J) (hC : (delta-d)*S = delta*d*P) :
    (delta*b*u-J)*E-delta*J*u = 0 := by
  apply (mul_eq_zero.mp ?_).resolve_left hp
  linear_combination b*u^2*hC-(delta-d)*b*u*hS+P*(E+delta*u)*hJ

end RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixAlphaTwoCompletion

open RKCert.ReviewedNative.DIRKOrderElevenInvisibleSixAlphaTwoCompletion
#print axioms counts
#print axioms genuine_fourth_read
#print axioms ordinary_det_zero
#print axioms adjacent_signal
