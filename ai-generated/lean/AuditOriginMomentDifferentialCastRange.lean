module

import RKCert.ReviewedNative.OriginMomentDifferentialCastRange

open Polynomial
open RKResearch.Certified.Graded.OriginMomentDifferential

/- Literal finite cast condition, with no characteristic typeclass. -/
example {K : Type*} [Field K] (D : ℕ) :
    NatCastsThrough K D ↔ (∀ m : ℕ, 0 < m → m ≤ D → (m : K) ≠ 0) :=
  Iff.rfl

example {K : Type*} [Field K] {n : ℕ} {P : K[X]}
    (H : Window n P) (d : P.natDegree ≤ n+1)
    (hz : NatCastsThrough K (2*n+1)) : P = 0 :=
  H.eq_zero_of_lower_degree_of_casts d hz

example {K : Type*} [Field K] {n : ℕ} {P : K[X]}
    (H : Window n P) (hp : P ≠ 0) (hz : NatCastsThrough K (2*n+2)) :
    ∃ s : K, (X * (1-X)) * P.derivative.derivative = P.derivative + C s * P :=
  H.exists_differential_scalar_of_casts hp hz

/- Independent local regular-ODE client, paying only the two multiplicity casts. -/
example {K : Type*} [Field K] {A B D P : K[X]} {u : K}
    (hp : P ≠ 0) (eq : A * P.derivative.derivative = B * P.derivative + D * P)
    (reg : A.eval u ≠ 0) (hu : P.eval u = 0)
    (paid : 1 < P.rootMultiplicity u →
      ((P.rootMultiplicity u : ℕ) : K) ≠ 0 ∧
        ((P.rootMultiplicity u - 1 : ℕ) : K) ≠ 0) : P.derivative.eval u ≠ 0 :=
  derivative_eval_ne_zero_of_regular_eq_of_casts hp eq reg hu paid

example {K : Type*} [Field K] {n : ℕ} {P : K[X]} {u : K}
    (H : Window n P) (hp : P ≠ 0) (hz : NatCastsThrough K (2*n+2))
    (u0 : u ≠ 0) (u1 : u ≠ 1) :
    (P.eval u = 0 → P.derivative.eval u ≠ 0) ∧
      (P.derivative.eval u = 0 → P.eval u ≠ 0) :=
  ⟨H.derivative_eval_ne_zero_of_casts hp hz u0 u1,
    H.eval_ne_zero_of_derivative_zero_of_casts hp hz u0 u1⟩

#print axioms RKResearch.Certified.Graded.OriginMomentDifferential.NatCastsThrough
#print axioms RKResearch.Certified.Graded.OriginMomentDifferential.Window.eq_zero_of_lower_degree_of_casts
#print axioms RKResearch.Certified.Graded.OriginMomentDifferential.Window.exists_differential_scalar_of_casts
#print axioms RKResearch.Certified.Graded.OriginMomentDifferential.derivative_eval_ne_zero_of_regular_eq_of_casts
#print axioms RKResearch.Certified.Graded.OriginMomentDifferential.Window.derivative_eval_ne_zero_of_casts
#print axioms RKResearch.Certified.Graded.OriginMomentDifferential.Window.eval_ne_zero_of_derivative_zero_of_casts
