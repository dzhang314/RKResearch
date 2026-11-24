module

public import RKCert.ReviewedNative.FiniteOrderCheck
public import RKCert.ReviewedNative.ChangeCoefficients
public import Mathlib.Algebra.QuadraticAlgebra.Basic

import Mathlib.Tactic.FinCases

@[expose] public section

/-! # Seven-stage order-six common-diagonal Runge–Kutta tableau

This exact tableau results from a four-stage Laguerre donor and a
three-stage weighted-adjoint Gauss suffix. It is verified below against
the full reviewed order predicate, without assuming any simplifying
conditions. The coefficients are not floating-point approximations. -/

namespace RKResearch.Certified.LaguerreGauss76

open FiniteRootedTree
open scoped Matrix

abbrev Q2 := QuadraticAlgebra ℚ 2 0

/-- The coefficient algebra, with generators whose squares are two and fifteen. -/
abbrev Coeff := QuadraticAlgebra Q2 15 0

/-- (a+b√ 2+c√{15}+d√{30}) in the two quadratic bases. -/
def coeff (a b c d : ℚ) : Coeff := ⟨⟨a,b⟩,⟨c,d⟩⟩

def gamma : Coeff := coeff (1/2) 0 0 0

/-- The seven physical stage rows in chronological order. -/
def A : Matrix (Fin 7) (Fin 7) Coeff := Matrix.of fun i j =>
  if i = j then gamma else
    match i.val, j.val with
    | 1, 0 => coeff (1/2) (-1/2) 0 0
    | 2, 0 => coeff (1/2) (1/2) 0 0
    | 3, 0 => coeff (-24470833/80062991) 0 (19621575/320251964) 0
    | 3, 1 => coeff (21127135/160125982) (134475663/1281007856) (-38197675/640503928) (-58325375/1281007856)
    | 3, 2 => coeff (21127135/160125982) (-134475663/1281007856) (-38197675/640503928) (58325375/1281007856)
    | 4, 1 => coeff (-1376833/3112530) (-3561209/12450120) (-997529/31125300) (-104319/5187550)
    | 4, 2 => coeff (-1376833/3112530) (3561209/12450120) (-997529/31125300) (104319/5187550)
    | 4, 3 => coeff (1376833/1556265) 0 (1276897/7781325) 0
    | 5, 1 => coeff (-98291/1556265) (-39553/2490024) (-1608041/31125300) (-190981/5187550)
    | 5, 2 => coeff (-98291/1556265) (39553/2490024) (-1608041/31125300) (190981/5187550)
    | 5, 3 => coeff (-1095641/10893855) 0 (638941/54469275) 0
    | 5, 4 => coeff (27/119) 0 (-1/119) 0
    | 6, 1 => coeff (1573415/4980048) (1879487/9960096) (260557/4980048) (14765/415004)
    | 6, 2 => coeff (1573415/4980048) (-1879487/9960096) (260557/4980048) (-14765/415004)
    | 6, 3 => coeff (-4271095/8715084) 0 (-478861/4357542) 0
    | 6, 4 => coeff (-135/952) 0 (-109/1904) 0
    | 6, 5 => coeff 0 0 (1/16) 0
    | _, _ => 0

/-- The donor stages have weight zero; all three Gauss weights are positive. -/
def b (i : Fin 7) : Coeff :=
  match i.val with
  | 4 | 5 => coeff (5/18) 0 0 0
  | 6 => coeff (4/9) 0 0 0
  | _ => 0

def c (i : Fin 7) : Coeff :=
  match i.val with
  | 0 => coeff (1/2) 0 0 0
  | 1 => coeff 1 (-1/2) 0 0
  | 2 => coeff 1 (1/2) 0 0
  | 3 => coeff (395/862) 0 (-25/431) 0
  | 4 => coeff (1/2) 0 (1/10) 0
  | 5 => coeff (1/2) 0 (-1/10) 0
  | _ => gamma

theorem row_sums : A *ᵥ 1 = c := by
  funext i
  exact (by decide +kernel : ∀ i : Fin 7, (A *ᵥ 1) i = c i) i

theorem lowerTriangular : A.IsLowerTriangular := by
  intro i j hij
  change i.val < j.val at hij
  fin_cases i <;> fin_cases j <;> first | rfl | norm_num at hij

theorem diagonal (i : Fin 7) : A i i = gamma := by simp [A]

theorem two_gamma : 2 * gamma = 1 := by decide +kernel

theorem diagonal_ne_zero : gamma ≠ 0 := by decide +kernel

/-- The order-seven bush gives (399/400), not one. The identity is cleared
of its denominator and therefore remains valid after coefficient transport. -/
theorem seventh_bush_scaled :
    400 * (((bushyTree 7).factorial : Coeff) * (b ⬝ᵥ Φ (bushyTree 7) A)) = 399 := by
  rw [factorial_bushyTree, Φ_bushyTree, row_sums]
  decide +kernel

theorem not_order_seven : ¬ HasOrder 7 A b := by
  intro h
  have ht := h (bushyTree 7) (by rw [order_bushyTree]; decide)
  have he := seventh_bush_scaled
  rw [ht, mul_one] at he
  exact (by decide +kernel : (400 : Coeff) ≠ 399) he

section Specialization

variable {K : Type*} [Field K] [CharZero K]

/-- Evaluate the rational coordinates at any chosen roots with squares
two and fifteen. This is a tower of Mathlib quadratic-algebra lifts. -/
def specialize (x y : K) (hx : x^2 = 2) (hy : y^2 = 15) : Coeff →+* K := by
  let f : Q2 →+* K := (QuadraticAlgebra.lift (R := ℚ) (a := 2) (b := 0)
    ⟨x, by simpa [sq, Algebra.smul_def] using hx⟩).toRingHom
  letI : Algebra Q2 K := f.toAlgebra
  exact (QuadraticAlgebra.lift (R := Q2) (a := 15) (b := 0)
    ⟨y, by simpa [sq, Algebra.smul_def, map_ofNat] using hy⟩).toRingHom

theorem map_gamma (f : Coeff →+* K) : f gamma = 1/2 := by
  have h : (2:K) * f gamma = 1 := by simpa only [map_mul, map_ofNat, map_one] using congrArg f two_gamma
  apply (eq_div_iff (by norm_num : (2:K) ≠ 0)).mpr
  simpa only [mul_comm] using h

/-- The next-order error remains nonzero in every characteristic-zero
specialization, regardless of whether injectivity is supplied. -/
theorem not_order_seven_map (f : Coeff →+* K) : ¬ HasOrder 7 (A.map f) (f ∘ b) := by
  intro h
  have ht := h (bushyTree 7) (by rw [order_bushyTree]; decide)
  have he : (400 : K) * (((bushyTree 7).factorial : K) *
      ((f ∘ b) ⬝ᵥ Φ (bushyTree 7) (A.map f))) = 399 := by
    simpa only [map_mul, map_natCast, map_ofNat, RingHom.map_dotProduct, map_Φ_coefficients]
      using congrArg f seventh_bush_scaled
  rw [ht, mul_one] at he
  norm_num at he

end Specialization
end RKResearch.Certified.LaguerreGauss76
