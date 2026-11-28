module
public import RKCert.ReviewedNative.DIRK12MidpointRealSupport
public import RKCert.ReviewedNative.DIRK12Q36RealScalar

@[expose] public section

/-! Exact scalar quadrature on the literal ten real labels, with a
transfer to any actual tableau whose nonzero weights aggregate to
these interpolation weights. Nonlinear tableau flags are separate. -/
namespace RKResearch.Certified.DIRK12MidpointRealInterval

open RKResearch Graded FiniteRootedTree Polynomial DirectedRatBox
open scoped Matrix Polynomial FiniteRootedTree BigOperators

noncomputable def scalarQuadrature (x f : ℝ) : ℝ[X] →ₗ[ℝ] ℝ :=
  PaidNodalQuadrature.quadr Finset.univ (site x f) integral

theorem exact_scalar_quadrature {x f : ℝ}
    (hx : Encloses xBox x) (hf : Encloses fBox f) (hx0 : realX x=0) (hf0 : realF x f=0)
    (q : ℝ[X]) (hq : q.natDegree<12) :
    scalarQuadrature x f q=integral q :=
  DIRK12Q36Moments.real_paid_scalar hx hf hx0 hf0
    (orientation_sum x f) (orientation_prod x f hx hf) (site x f)
    (site_distinct hx hf) (support_nodal_eq x f) q hq

theorem exists_scalar_quadrature :
    ∃ x f : ℝ, Encloses xBox x ∧ Encloses fBox f ∧ realX x=0 ∧ realF x f=0 ∧
      Function.Injective (site x f) ∧
      (∀ q : ℝ[X], q.natDegree<12 → scalarQuadrature x f q=integral q) := by
  obtain ⟨x,f,hx,hf,hx0,hf0⟩ := exists_real_parameters
  exact ⟨x,f,hx,hf,hx0,hf0,site_distinct hx hf,exact_scalar_quadrature hx hf hx0 hf0⟩

variable {ι : Type*} [Fintype ι]

/-- The actual finite weights may split at repeated sites and may
vanish at additional ghost nodes. Only the aggregate at each of the
ten labels must equal its cardinal quadrature weight. -/
theorem quadrature_of_aggregate {x f : ℝ} (A : Matrix ι ι ℝ) (b : ι → ℝ) (tag : ι → Fin 10)
    (clocks : ∀ i, b i ≠ 0 → 1-nodes A i=site x f (tag i))
    (weights : ∀ j : Fin 10, (∑ i, if tag i=j then b i else 0)
      = integral (Lagrange.basis Finset.univ (site x f) j))
    (q : ℝ[X]) :
    DIRK12MidpointStar.quadr A b q=scalarQuadrature x f q := by
  classical
  rw [DIRK12MidpointStar.quadr_apply,scalarQuadrature,PaidNodalQuadrature.quadr_apply]
  calc
    (∑ i, b i*q.eval (1-nodes A i)) = ∑ i, b i*q.eval (site x f (tag i)) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases zero : b i=0
      · simp [zero]
      · rw [clocks i zero]
    _ = ∑ i, ∑ j : Fin 10, if tag i=j then b i*q.eval (site x f j) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      simp
    _ = ∑ j : Fin 10, (∑ i, if tag i=j then b i else 0)*q.eval (site x f j) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      by_cases t : tag i=j <;> simp [t]
    _ = _ := by simp only [weights]

theorem actual_scalar_and_star {x f : ℝ}
    (hx : Encloses xBox x) (hf : Encloses fBox f) (hx0 : realX x=0) (hf0 : realF x f=0)
    (A : Matrix ι ι ℝ) (b : ι → ℝ) (tag : ι → Fin 10)
    (clocks : ∀ i, b i≠0 → 1-nodes A i=site x f (tag i))
    (weights : ∀ j : Fin 10, (∑ i, if tag i=j then b i else 0)
      = integral (Lagrange.basis Finset.univ (site x f) j)) :
    (∀ q : ℝ[X], q.natDegree<12 → DIRK12MidpointStar.quadr A b q=integral q) ∧
    (starLo:ℝ) < (((bushyTree 13).factorial:Nat):ℝ)*(b ⬝ᵥ Φ (bushyTree 13) A)-1 ∧
      (((bushyTree 13).factorial:Nat):ℝ)*(b ⬝ᵥ Φ (bushyTree 13) A)-1 < (starHi:ℝ) := by
  have paid : ∀ q : ℝ[X], q.natDegree<12 → DIRK12MidpointStar.quadr A b q=integral q := by
    intro q hq
    rw [quadrature_of_aggregate A b tag clocks weights]
    exact exact_scalar_quadrature hx hf hx0 hf0 q hq
  refine ⟨paid,actual_star_bounded A b hx hf (orientation_sum x f) (orientation_prod x f hx hf) ?_ paid⟩
  intro i
  by_cases zero : b i=0
  · simp [zero]
  · rw [clocks i zero,← support_nodal_eq,
      Lagrange.eval_nodal_at_node (Finset.mem_univ (tag i)),mul_zero]

end RKResearch.Certified.DIRK12MidpointRealInterval

#print axioms RKResearch.Certified.DIRK12MidpointRealInterval.exists_scalar_quadrature
#print axioms RKResearch.Certified.DIRK12MidpointRealInterval.actual_scalar_and_star
