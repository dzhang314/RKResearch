module

public import RKCert.ReviewedNative.PositiveIntervalGrid19

@[expose] public section

/-! # Twelve paid scalar moments for the weak-five chart -/
namespace RKCert.ReviewedNative.WeakFive16

open Polynomial RKCert.ReviewedNative.PositiveRule19

variable {K : Type*} [Field K]

/-- The non-origin part of the five-clock nodal mask. -/
noncomputable def nodalTail (c : Fin 5 → K) (Z : K[X]) : K[X] :=
  (X - C (c 1)) * (X - C (c 4)) * Z

variable [CharZero K]

/-- The labels are physical, not in numerical order. In order, their
forward clocks are 0, u, a, h, z. The middle quadratic uses a and h. -/
structure Moments (q Z : K[X]) (c : Fin 5 → K) : Prop where
  qNonzero : q ≠ 0
  qDegree : q.natDegree ≤ 4
  origin : c 0 = 0
  clockSimple : Function.Injective c
  active : ∀ i, c i ≠ 1 ∧ q.eval (c i) ≠ 0
  middleFactor : Z = (X - C (c 2)) * (X - C (c 3))
  forwardFirst : integral 0 (c 1) (X * q) = 0
  forwardSecond : integral 0 (c 1) (X^2 * q) = 0
  forwardInner : integral 0 (c 2) (X * (X - C (c 1)) * q) = 0
  reverseFirst : integral (c 4) 1 ((1-X) * q) = 0
  reverseSecond : integral (c 4) 1 ((1-X)^2 * q) = 0
  reverseInner : integral (c 3) 1 ((1-X) * (C (c 4) - X) * q) = 0
  weightedMoments : ∀ H : K[X], H.natDegree ≤ 5 →
    integral 0 1 ((X * (1-X)) * (q * nodalTail c Z) * H) = 0

theorem Moments.clock_ne_zero {q Z : K[X]} {c : Fin 5 → K}
    (M : Moments q Z c) {i : Fin 5} (hi : i ≠ 0) : c i ≠ 0 :=
  fun e => hi (M.clockSimple (e.trans M.origin.symm))

theorem Moments.q_at_origin {q Z : K[X]} {c : Fin 5 → K}
    (M : Moments q Z c) : q.eval 0 ≠ 0 := by
  simpa only [M.origin] using (M.active 0).2

end RKCert.ReviewedNative.WeakFive16
