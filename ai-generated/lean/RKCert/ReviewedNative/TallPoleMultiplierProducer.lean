module

public import RKCert.ReviewedNative.TallPoleMultiplierWindow
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Algebra.EuclideanDomain.Basic

import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Optional Euclidean cofactor producer for the finite pole-window bound

This is separate from the window consumer. The degree is the base-field
quotient degree; identification with the geometric root count is not a
formalized assertion in this module. -/

namespace RKResearch.Certified.TallFiniteResponse

open RKResearch Polynomial
open scoped Matrix Polynomial

noncomputable section

variable {K : Type*} [Field K] {Q G V B : K[X]}

private theorem factor_nonzero (hQ : Q ≠ 0) (hq : Q = G*V) : G ≠ 0 ∧ V ≠ 0 := by
  have hprod : G*V ≠ 0 := by rw [← hq]; exact hQ
  exact mul_ne_zero_iff.mp hprod

/-- Independent factorization producer. No implementation of gcd and no
condition on the roots is needed to read these two cofactor identities. -/
theorem PoleMultiplier.of_derivative_factors (hQ : Q ≠ 0) (hq : Q = G*V)
    (hd : Q.derivative = G*B) : PoleMultiplier Q V.natDegree V B := by
  obtain ⟨hG, hV⟩ := factor_nonzero hQ hq
  have htop : V.coeff V.natDegree ≠ 0 := by
    rw [Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hV
  have hcross : V*Q.derivative = B*Q := by
    calc
      V*Q.derivative = V*(G*B) := congrArg (fun f : K[X] => V*f) hd
      _ = B*(G*V) := by ring
      _ = B*Q := congrArg (fun f : K[X] => B*f) hq.symm
  have hB : B.natDegree ≤ V.natDegree ∧ B.coeff V.natDegree = 0 := by
    by_cases hB0 : B = 0
    · rw [hB0, Polynomial.natDegree_zero, Polynomial.coeff_zero]
      exact ⟨Nat.zero_le _, rfl⟩
    · have hQd : Q.derivative ≠ 0 := by
        rw [hd]
        exact mul_ne_zero hG hB0
      have hQdeg : Q.natDegree ≠ 0 := fun hz => hQd (Polynomial.derivative_of_natDegree_zero hz)
      have hlt := Polynomial.natDegree_derivative_lt hQdeg
      have hdegQ : Q.natDegree = G.natDegree+V.natDegree := by
        rw [hq, Polynomial.natDegree_mul hG hV]
      have hdegD : Q.derivative.natDegree = G.natDegree+B.natDegree := by
        rw [hd, Polynomial.natDegree_mul hG hB0]
      have hBd : B.natDegree < V.natDegree := by omega
      exact ⟨hBd.le, Polynomial.coeff_eq_zero_of_natDegree_lt hBd⟩
  exact PoleMultiplier.of_boundary hcross le_rfl hB.1 htop hB.2

/-- The finite degree difference specified by an ordinary Euclidean gcd.
This definition alone does not assert a root-count or characteristic-zero
factorization theorem. -/
def derivativeGcdQuotientDegree (Q : K[X]) : ℕ := by
  classical
  exact Q.natDegree - (EuclideanDomain.gcd Q Q.derivative).natDegree

theorem exists_pole_multiplier_of_gcd (Q : K[X]) (hQ : Q ≠ 0) :
    ∃ V B : K[X], PoleMultiplier Q (derivativeGcdQuotientDegree Q) V B := by
  classical
  let G := EuclideanDomain.gcd Q Q.derivative
  have hq0 : G ∣ Q := EuclideanDomain.gcd_dvd_left Q Q.derivative
  have hd0 : G ∣ Q.derivative := EuclideanDomain.gcd_dvd_right Q Q.derivative
  obtain ⟨V,hq⟩ := hq0
  obtain ⟨B,hd⟩ := hd0
  obtain ⟨hG,hV⟩ := factor_nonzero hQ hq
  have heq : Q.natDegree = G.natDegree+V.natDegree := by
    rw [hq, Polynomial.natDegree_mul hG hV]
  have hquot : derivativeGcdQuotientDegree Q = V.natDegree := by
    change Q.natDegree-G.natDegree = V.natDegree
    omega
  rw [hquot]
  exact ⟨V,B,PoleMultiplier.of_derivative_factors hQ hq hd⟩

variable {s p : ℕ} {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K} {P : K[X]}

/-- The base-field gcd-degree version, with no external multiplier input.
A reduced `Fraction` is needed only to interpret the remaining poles. -/
theorem Fraction.order_le_num_add_derivativeGcd [CharZero K] (hf : Fraction A b P Q)
    (ho : HasOrder p A b) : p ≤ P.natDegree+derivativeGcdQuotientDegree Q := by
  have hQ : Q ≠ 0 := by
    intro hz
    have he := hf.den_zero
    rw [hz, Polynomial.coeff_zero] at he
    exact zero_ne_one he
  obtain ⟨V,B,hm⟩ := exists_pole_multiplier_of_gcd Q hQ
  exact hf.order_le_num_add_of_multiplier hm ho

end
end RKResearch.Certified.TallFiniteResponse
