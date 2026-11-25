module

import RKCert.ReviewedNative.OriginMomentDifferential

open Polynomial
open RKResearch.Certified.Graded.OriginMomentDifferential

/- Exact conversion from ordinary power moments, before any characteristic restriction. -/
example {K : Type*} [Field K] {n : ℕ} {P : K[X]}
    (d : P.natDegree ≤ n+2) (h0 : P.eval 0 = 0) (h1 : P.derivative.eval 0 = 0)
    (test : ∀ k < n, integral01 (X^k * P) = 0) : Window n P :=
  Window.of_power d h0 h1 test

example {K : Type*} [Field K] [CharZero K] {n : ℕ} {P : K[X]}
    (H : Window n P) (d : P.natDegree ≤ n+1) : P = 0 :=
  H.eq_zero_of_lower_degree d

example {K : Type*} [Field K] [CharZero K] {n : ℕ} {P : K[X]}
    (H : Window n P) (hp : P ≠ 0) :
    ∃ s : K, (X * (1-X)) * P.derivative.derivative = P.derivative + C s * P :=
  H.exists_differential_scalar hp

/- The independent regular-ODE criterion does not assume a moment window. -/
example {K : Type*} [Field K] [CharZero K] {A B D P : K[X]} {u : K}
    (hp : P ≠ 0) (eq : A * P.derivative.derivative = B * P.derivative + D * P)
    (reg : A.eval u ≠ 0) (hu : P.eval u = 0) : P.derivative.eval u ≠ 0 :=
  derivative_eval_ne_zero_of_regular_eq hp eq reg hu

example {K : Type*} [Field K] [CharZero K] {n : ℕ} {P : K[X]} {u : K}
    (H : Window n P) (hp : P ≠ 0) (u0 : u ≠ 0) (u1 : u ≠ 1) :
    (P.eval u = 0 → P.derivative.eval u ≠ 0) ∧
      (P.derivative.eval u = 0 → P.eval u ≠ 0) :=
  ⟨H.derivative_eval_ne_zero hp u0 u1, H.eval_ne_zero_of_derivative_zero hp u0 u1⟩

#print axioms RKResearch.Certified.Graded.OriginMomentDifferential.Window.of_power
#print axioms RKResearch.Certified.Graded.OriginMomentDifferential.Window.eq_zero_of_lower_degree
#print axioms RKResearch.Certified.Graded.OriginMomentDifferential.Window.exists_differential_scalar
#print axioms RKResearch.Certified.Graded.OriginMomentDifferential.derivative_eval_ne_zero_of_regular_eq
#print axioms RKResearch.Certified.Graded.OriginMomentDifferential.Window.derivative_eval_ne_zero
#print axioms RKResearch.Certified.Graded.OriginMomentDifferential.Window.eval_ne_zero_of_derivative_zero
