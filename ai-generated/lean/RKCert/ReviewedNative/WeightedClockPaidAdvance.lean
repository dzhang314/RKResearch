module

public import RKCert.ReviewedNative.LocalLinearJointBands
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.EraseLead

@[expose] public section

/-! # One more paid test on an actual weighted clock

A paid new top degree extends the entire lower polynomial band. A paid
rational advance extends tests by one through division by X-C a. Signed
mass tests count nonzero *whole-clock* sums, not nonzero physical rows. -/
namespace RKResearch.Certified.Graded.Reverse.LocalLinear

open RKResearch Module Polynomial RKCert.Endpoint RKCert.Endpoint.WeightedClock
open scoped Classical Matrix BigOperators
noncomputable section

variable {K : Type*} [Field K] {s : ℕ}
variable {y w v : Fin s → K} {M : Submodule K (Fin s → K)} {d : ℕ}

theorem clock_linear_quotient_degree (P : K[X]) (a : K) :
    (P /ₘ (X-C a)).natDegree = P.natDegree-1 := by
  rw [natDegree_divByMonic _ (monic_X_sub_C a), natDegree_X_sub_C]

theorem clock_linear_quotient_identity (P : K[X]) (a : K) :
    C (P.eval a) + (X-C a) * (P /ₘ (X-C a)) = P := by
  conv_rhs => rw [←modByMonic_add_div P (X-C a), modByMonic_X_sub_C_eq_C_eval]

/-- A single paid test of exact degree `d+1` supplies all degree-`d+1`
tests, provided the full lower band has already been paid. -/
theorem weighted_tests_one_more_of_top
    (lower : ∀ P : K[X], P.natDegree ≤ d → weightedEval y w P ∈ M)
    {Q : K[X]} (qd : Q.natDegree = d+1) (top : weightedEval y w Q ∈ M) :
    ∀ P : K[X], P.natDegree ≤ d+1 → weightedEval y w P ∈ M := by
  have Qd : Q.eraseLead.natDegree ≤ d := by
    have q := eraseLead_natDegree_le Q
    rw [qd] at q
    omega
  have Qn : Q ≠ 0 := by
    intro eq
    rw [eq, natDegree_zero] at qd
    omega
  have lead : Q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr Qn
  have sQ : Q.eraseLead + Q.leadingCoeff • (X^(d+1) : K[X]) = Q := by
    rw [smul_eq_C_mul, ←qd, eraseLead_add_C_mul_X_pow]
  have raw : Q.leadingCoeff • weightedEval y w (X^(d+1)) ∈ M := by
    have eq : Q.leadingCoeff • weightedEval y w (X^(d+1)) =
        weightedEval y w Q - weightedEval y w Q.eraseLead := by
      apply eq_sub_iff_add_eq.mpr
      rw [←map_smul, ←map_add, add_comm, sQ]
    rw [eq]
    exact M.sub_mem top (lower _ Qd)
  have one : weightedEval y w (X^(d+1)) ∈ M := by
    have z := M.smul_mem Q.leadingCoeff⁻¹ raw
    rwa [smul_smul, inv_mul_cancel₀ lead, one_smul] at z
  intro P pd
  by_cases small : P.natDegree ≤ d
  · exact lower P small
  have pe : P.natDegree = d+1 := by omega
  have ed : P.eraseLead.natDegree ≤ d := by
    have q := eraseLead_natDegree_le P
    rw [pe] at q
    omega
  have eq : P.eraseLead + P.leadingCoeff • (X^(d+1) : K[X]) = P := by
    rw [smul_eq_C_mul, ←pe, eraseLead_add_C_mul_X_pow]
  rw [←eq, map_add, map_smul]
  exact M.add_mem (lower _ ed) (M.smul_mem _ one)

/-- `(y-a)·v=w` and a paid v extend every paid weighted w polynomial
by one degree for v, without dividing at any physical row. -/
theorem weighted_tests_one_more_of_linear_advance (a : K) (base : v ∈ M)
    (advance : ∀ i, (y i-a)*v i = w i)
    (lower : ∀ P : K[X], P.natDegree ≤ d → weightedEval y w P ∈ M) :
    ∀ P : K[X], P.natDegree ≤ d+1 → weightedEval y v P ∈ M := by
  intro P pd
  let R := P /ₘ (X-C a)
  have rd : R.natDegree ≤ d := by
    change (P /ₘ (X-C a)).natDegree ≤ d
    rw [clock_linear_quotient_degree]
    omega
  have factor : weightedEval y v P = P.eval a • v + weightedEval y w R := by
    ext i
    rw [weightedEval_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, weightedEval_apply]
    have eq := congrArg (fun G : K[X] => G.eval (y i)) (clock_linear_quotient_identity P a)
    change (C (P.eval a)+(X-C a)*R).eval (y i)=P.eval (y i) at eq
    simp only [eval_add, eval_mul, eval_sub, eval_X, eval_C] at eq
    rw [←advance i, ←eq]
    ring
  rw [factor]
  exact M.add_mem (M.smul_mem _ base) (lower R rd)

/-- A complete weighted band is paid as soon as its actual support
fits the available polynomial tests. -/
theorem completeOrbit_le_of_paid_tests
    (small : (weightedSites y w).card ≤ d+1)
    (tests : ∀ P : K[X], P.natDegree ≤ d → weightedEval y w P ∈ M) :
    completeOrbit y w ≤ M := by
  rw [completeOrbit, ←weightedBand_eq_range y w (d+1) small]
  intro x hx
  obtain ⟨P, pd, rfl⟩ := mem_weightedBand.mp hx
  apply tests
  by_cases z : P = 0
  · simp [z]
  have low := (natDegree_lt_iff_degree_lt z).mpr pd
  omega

/-- Signed grouping plus Lagrange interpolation. The size condition
only counts clocks with nonzero total mass. Thus a proved zero mass at
one exceptional live clock refunds one test. -/
theorem clock_masses_zero_of_significant_sites
    (tests : ∀ P : K[X], P.natDegree ≤ d → (∑ i, w i * P.eval (y i)) = 0)
    (small : ((weightedSites y w).filter fun a => clockMass y w a ≠ 0).card ≤ d+1) :
    ∀ a, clockMass y w a = 0 := by
  let D := (weightedSites y w).filter fun a => clockMass y w a ≠ 0
  intro a
  by_contra live
  have site : a ∈ weightedSites y w := by
    by_contra no
    exact live (clockMass_zero_of_not_site no)
  have ina : a ∈ D := Finset.mem_filter.mpr ⟨site, live⟩
  obtain ⟨i, _, hi⟩ := mem_weightedSites.mp site
  have ambient : a ∈ Finset.univ.image y := Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩
  let P := Lagrange.basis D id a
  have pd : P.natDegree ≤ d := by
    have e := Lagrange.natDegree_basis (Set.injOn_id _) ina
    change P.natDegree = D.card-1 at e
    change D.card ≤ d+1 at small
    omega
  have moment := tests P pd
  rw [weighted_sum_by_clock y w P.eval, Finset.sum_eq_single_of_mem a ambient] at moment
  · have evala : P.eval a = 1 := Lagrange.eval_basis_self (Set.injOn_id _) ina
    rw [evala, mul_one] at moment
    exact live moment
  · intro x _ xa
    by_cases yes : x ∈ D
    · have ev : P.eval x = 0 := Lagrange.eval_basis_of_ne (v:=id) xa.symm yes
      rw [ev, mul_zero]
    · have off : clockMass y w x = 0 := by
        by_contra xlive
        have xs : x ∈ weightedSites y w := by
          by_contra no
          exact xlive (clockMass_zero_of_not_site no)
        exact yes (Finset.mem_filter.mpr ⟨xs, xlive⟩)
      rw [off, zero_mul]

end
end RKResearch.Certified.Graded.Reverse.LocalLinear
