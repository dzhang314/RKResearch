module

public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.OfFn
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

/-! # Formal primitive and the Hermite nodal matrix

All abscissae are in an arbitrary characteristic-zero field. Evaluations of
the formal primitive are algebraic; there is no positivity or Rolle assumption.
We reuse the native multiplicity/root theorem and finite product divisibility. -/
namespace RKCert.Endpoint
open Polynomial
open scoped Classical

noncomputable section
variable {K : Type*} [Field K]

/-- Antiderivative with prescribed constant coefficient zero. -/
def formalPrimitive (P : K[X]) : K[X] :=
  ∑ i ∈ P.support, monomial (i+1) (P.coeff i / (i+1:K))

@[simp] theorem formalPrimitive_eval_zero (P : K[X]) :
    (formalPrimitive P).eval 0 = 0 := by
  simp [formalPrimitive, eval_finsetSum, eval_monomial]

variable [CharZero K]

@[simp] theorem derivative_formalPrimitive (P : K[X]) :
    (formalPrimitive P).derivative = P := by
  rw [formalPrimitive, map_sum]
  conv_rhs => rw [P.as_sum_support]
  apply Finset.sum_congr rfl
  intro i hi
  have hn : (i:K)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero i
  simp [div_mul_cancel₀ _ hn]

theorem natDegree_formalPrimitive_le (P : K[X]) :
    (formalPrimitive P).natDegree ≤ P.natDegree+1 := by
  have h := Polynomial.natDegree_derivative (formalPrimitive P)
  rw [derivative_formalPrimitive] at h
  omega

/-- The monic square-free polynomial of the old nodes, including the zero node. -/
def nodalHull (S : Finset K) : K[X] := ∏ a ∈ S, (X - C a)

omit [CharZero K] in
theorem monic_nodalHull (S : Finset K) : (nodalHull S).Monic :=
  monic_prod_X_sub_C id S

omit [CharZero K] in
@[simp] theorem natDegree_nodalHull (S : Finset K) : (nodalHull S).natDegree = S.card :=
  natDegree_finsetProd_X_sub_C_eq_card S id

omit [CharZero K] in
theorem nodalHull_eval_of_mem {S : Finset K} {a : K} (ha : a ∈ S) :
    (nodalHull S).eval a = 0 := by
  rw [nodalHull, eval_prod]
  apply Finset.prod_eq_zero ha
  simp

omit [CharZero K] in
/-- Finite Hermite root counting with one extra simple root. -/
theorem nodalHull_sq_extra_dvd (S : Finset K) {z : K} (hz : z ∉ S) {F : K[X]}
    (hv : ∀ a ∈ S, F.IsRoot a) (hd : ∀ a ∈ S, F.derivative.IsRoot a)
    (he : F.IsRoot z) : nodalHull S ^ 2 * (X - C z) ∣ F := by
  classical
  by_cases hf : F = 0
  · simp [hf]
  have hsq (a : K) (ha : a ∈ S) : (X - C a)^2 ∣ F :=
    (le_rootMultiplicity_iff hf).mp ((one_lt_rootMultiplicity_iff_isRoot hf).mpr ⟨hv a ha,hd a ha⟩)
  have hh : (∏ a ∈ S, (X - C a)^2) ∣ F :=
    Finset.prod_dvd_of_coprime (fun a _ b _ hn =>
      (isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hn).isUnit).pow) hsq
  rw [nodalHull, ← Finset.prod_pow]
  apply IsCoprime.mul_dvd _ hh (dvd_iff_isRoot.mpr he)
  apply IsCoprime.prod_left
  intro a ha
  exact (isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr (ne_of_mem_of_not_mem ha hz)).isUnit).pow_left

/-- Nonsingularity of the genuine nodal observation matrix, with one new knot
`z` following the r−1 old nonzero knots. Only those r nonzero endpoints are
sampled: vanishing at zero is a theorem about the normalized primitive. -/
theorem nodal_primitive_zero (S : Finset K) {z : K} (hz : z ∉ S)
    (Q : K[X]) (hdeg : Q.natDegree < S.card)
    (obs : ∀ a ∈ S, a ≠ 0 → (formalPrimitive (nodalHull S * Q)).IsRoot a)
    (obsZ : (formalPrimitive (nodalHull S * Q)).IsRoot z) : Q=0 := by
  let F := formalPrimitive (nodalHull S * Q)
  have hv (a : K) (ha : a ∈ S) : F.IsRoot a := by
    by_cases h : a = 0
    · subst a; exact formalPrimitive_eval_zero _
    · exact obs a ha h
  have hd (a : K) (ha : a ∈ S) : F.derivative.IsRoot a := by
    dsimp only [F]
    rw [derivative_formalPrimitive]
    simp [IsRoot, nodalHull_eval_of_mem ha]
  have hdiv := nodalHull_sq_extra_dvd S hz hv hd obsZ
  have hF : F.natDegree ≤ 2*S.card := by
    have h1 := natDegree_formalPrimitive_le (nodalHull S*Q)
    have h2 := natDegree_mul_le (p := nodalHull S) (q := Q)
    rw [natDegree_nodalHull] at h2
    dsimp only [F]; omega
  have hprod : (nodalHull S^2*(X-C z)).natDegree = 2*S.card+1 := by
    rw [natDegree_mul (pow_ne_zero _ (monic_nodalHull S).ne_zero) (monic_X_sub_C z).ne_zero,
      natDegree_pow, natDegree_nodalHull, natDegree_X_sub_C]
  have zero : F=0 := eq_zero_of_dvd_of_natDegree_lt hdiv (by omega)
  have dz := congrArg Polynomial.derivative zero
  simpa [F, (monic_nodalHull S).ne_zero] using dz

/-- A polynomial is determined by its derivative and its value at zero. -/
theorem eq_of_derivative_and_eval_zero {P T : K[X]} (hd : P.derivative = T.derivative)
    (hv : P.eval 0 = T.eval 0) : P = T := by
  have hh : (P-T).derivative = 0 := by rw [map_sub,hd,sub_self]
  have hc : (P-T).coeff 0 = 0 := by rw [coeff_zero_eq_eval_zero,eval_sub,hv,sub_self]
  have hx := eq_C_of_derivative_eq_zero hh
  rw [hc,C_0] at hx
  exact sub_eq_zero.mp hx

/-- Linear map of normalized formal integration; this is not an analytic integral. -/
def formalPrimitiveLinear : K[X] →ₗ[K] K[X] where
  toFun := formalPrimitive
  map_add' v w := eq_of_derivative_and_eval_zero (by simp) (by simp)
  map_smul' s w := eq_of_derivative_and_eval_zero (by simp) (by simp)

/-- Nonzero knots at which the square nodal matrix is observed. -/
def observationKnots (S : Finset K) (z : K) := insert z (S.erase 0)

/-- The actual nodal matrix as a linear map on r polynomial coefficients. -/
def nodalObservations (S : Finset K) (z : K) :
    (Fin S.card → K) →ₗ[K] (observationKnots S z → K) :=
  (LinearMap.pi fun a : observationKnots S z => Polynomial.leval a.val).comp
    (formalPrimitiveLinear.comp ((LinearMap.mulLeft K (nodalHull S)).comp (ofFn S.card)))

/-- Full nonsingularity of the finite Hermite moment matrix, with no order
structure on the knots. Both the domain and actual nonzero target have r coordinates. -/
theorem nodalObservations_bijective {S : Finset K} (h0 : (0:K) ∈ S) {z : K}
    (hz : z ∉ S) : Function.Bijective (nodalObservations S z) := by
  classical
  have size : (observationKnots S z).card=S.card := by
    rw [observationKnots,Finset.card_insert_of_notMem,Finset.card_erase_add_one h0]
    exact fun hh => hz (Finset.mem_of_mem_erase hh)
  have hin : Function.Injective (nodalObservations S z) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    have obs (a : K) (ha : a ∈ observationKnots S z) :
        (formalPrimitive (nodalHull S * ofFn S.card v)).eval a=0 :=
      congrFun hv ⟨a,ha⟩
    apply injective_ofFn S.card
    rw [map_zero]
    apply nodal_primitive_zero S hz _ (ofFn_natDegree_lt (Finset.card_pos.mpr ⟨0,h0⟩) v)
    · intro a ha hne
      exact obs _ (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hne,ha⟩))
    · exact obs _ (Finset.mem_insert_self _ _)
  refine ⟨hin, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hin⟩
  simp only [Module.finrank_pi, Fintype.card_fin, Fintype.card_coe, size]

end
end RKCert.Endpoint
