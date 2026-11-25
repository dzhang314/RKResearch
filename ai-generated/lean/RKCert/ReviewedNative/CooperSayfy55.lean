module

public import RKCert.ReviewedNative.FiniteOrderCheck
public import RKCert.ReviewedNative.ChangeCoefficients
public import Mathlib.Algebra.QuadraticAlgebra.Basic

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

@[expose] public section

/-!
# Cooper–Sayfy's five-stage fifth-order singly diagonally implicit method

The primary tableau is on p. 551 of G. J. Cooper and A. Sayfy, *Semiexplicit
A-stable Runge-Kutta methods*, Math. Comp. 33 (1979), 541–556,
doi:10.1090/S0025-5718-1979-0521275-1. In their indexing the sixth row
outputs the step and is not another stage. We encode the five stages exactly
over Mathlib's quadratic algebra with generator squared equal to six. The
entire positive certificate uses the existing checker on the reviewed trees.
-/

namespace RKResearch.Certified.CooperSayfy55

open FiniteRootedTree
open scoped Matrix

/-- Coordinates `u + v·ω` with `ω² = 6`. No square-root approximation is used. -/
abbrev Q6 := QuadraticAlgebra ℚ 6 0

/-- The printed coefficient `(u + v·ω)/d` as exact rational coordinates. -/
def coeff (u v d : ℚ) : Q6 := ⟨u / d, v / d⟩

def gamma : Q6 := coeff 6 (-1) 10

def A : Matrix (Fin 5) (Fin 5) Q6 := Matrix.of fun i j =>
  if i = j then gamma else
    match i.val, j.val with
    | 1, 0 => coeff (-6) 5 14
    | 2, 0 => coeff 888 607 2850
    | 2, 1 => coeff 126 (-161) 1425
    | 3, 0 => coeff 3153 (-3082) 14250
    | 3, 1 => coeff 3213 1148 28500
    | 3, 2 => coeff (-267) 88 500
    | 4, 0 => coeff (-32583) 14638 71250
    | 4, 1 => coeff (-17199) 364 142500
    | 4, 2 => coeff 1329 (-544) 2500
    | 4, 3 => coeff (-96) 131 625
    | _, _ => 0

def b (i : Fin 5) : Q6 :=
  match i.val with
  | 2 => coeff 1 0 9
  | 3 => coeff 16 (-1) 36
  | 4 => coeff 16 1 36
  | _ => 0

/-- The abscissae printed independently beside the stage rows. -/
def c (i : Fin 5) : Q6 :=
  match i.val with
  | 0 => gamma
  | 1 => coeff 6 9 35
  | 2 => 1
  | 3 => coeff 4 (-1) 10
  | _ => coeff 4 1 10

theorem row_sums : A *ᵥ 1 = c := by
  funext i
  exact (by decide +kernel : ∀ i : Fin 5, (A *ᵥ 1) i = c i) i

theorem lowerTriangular : A.IsLowerTriangular := by
  intro i j hij
  change i.val < j.val at hij
  fin_cases i <;> fin_cases j <;> first | rfl | norm_num at hij

theorem diagonal (i : Fin 5) : A i i = gamma := by
  simp [A]

theorem diagonal_ne_zero : gamma ≠ 0 := by decide +kernel

set_option maxHeartbeats 2000000 in
theorem order_five : HasOrder 5 A b := by
  apply (checkOrder_iff A b 5).mp
  decide +kernel

/-- The order-six bush has scaled weight `101/100`, not `1`. The statement
clears its denominator so it transports through an arbitrary ring hom. -/
theorem sixth_bush_scaled :
    100 * (((bushyTree 6).factorial : Q6) * (b ⬝ᵥ Φ (bushyTree 6) A)) = 101 := by
  rw [factorial_bushyTree, Φ_bushyTree, row_sums]
  decide +kernel

theorem not_order_six : ¬ HasOrder 6 A b := by
  intro h
  have ht := h (bushyTree 6) (by rw [order_bushyTree]; decide)
  have he := sixth_bush_scaled
  rw [ht, mul_one] at he
  exact (by decide +kernel : (100 : Q6) ≠ 101) he

section Specialize

variable {K : Type*} [Field K] [CharZero K]

/-- Evaluate central rational coordinates at either square root of six.
The positive real root gives the published tableau. -/
def specialize (x : K) (hx : x^2 = 6) : Q6 →+* K :=
  (QuadraticAlgebra.lift (R := ℚ) (a := 6) (b := 0) ⟨x, by
    simpa [sq, Algebra.smul_def] using hx⟩).toRingHom

theorem specialize_coeff (x : K) (hx : x^2 = 6) (u v d : ℚ) :
    specialize x hx (coeff u v d) = (u : K)/(d : K) + (v : K)/(d : K)*x := by
  change (u/d) • (1 : K) + (v/d) • x = _
  simp [Algebra.smul_def]

theorem specialize_gamma (x : K) (hx : x^2 = 6) :
    specialize x hx gamma = (6-x)/10 := by
  rw [gamma, specialize_coeff]
  norm_num
  ring

theorem specialize_gamma_ne_zero (x : K) (hx : x^2 = 6) :
    specialize x hx gamma ≠ 0 := by
  rw [specialize_gamma]
  intro h
  have he : x = 6 := by linear_combination (-10)*h
  rw [he] at hx
  norm_num at hx

/-- This certificate does not require injectivity of the specialization:
the next-order discrepancy is rational and stays nonzero in characteristic zero. -/
theorem not_order_six_map (f : Q6 →+* K) : ¬ HasOrder 6 (A.map f) (f ∘ b) := by
  intro h
  have ht := h (bushyTree 6) (by rw [order_bushyTree]; decide)
  have he : (100 : K) * (((bushyTree 6).factorial : K) *
      ((f ∘ b) ⬝ᵥ Φ (bushyTree 6) (A.map f))) = 101 := by
    simpa only [map_mul, map_natCast, map_ofNat, RingHom.map_dotProduct, map_Φ]
      using congrArg f sixth_bush_scaled
  rw [ht, mul_one] at he
  norm_num at he

/-- Exact order and the strict SDIRK shape for the explicitly specialized tableau. -/
theorem specialized_exact (x : K) (hx : x^2 = 6) :
    let f := specialize x hx
    (A.map f).IsLowerTriangular ∧ (∀ i, (A.map f) i i = f gamma) ∧ f gamma ≠ 0 ∧
      HasOrder 5 (A.map f) (f ∘ b) ∧ ¬ HasOrder 6 (A.map f) (f ∘ b) := by
  let f := specialize x hx
  exact ⟨lowerTriangular.map f, fun i => congrArg f (diagonal i),
    specialize_gamma_ne_zero x hx, order_five.map f, not_order_six_map f⟩

end Specialize

end RKResearch.Certified.CooperSayfy55
