module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

/-! # Signed polynomial readout of finite weighted nodes

Weights are arbitrary field elements. This declaration is independent
of an order, a mask, a cut, or a distinction between stage clocks. -/
namespace RKResearch.Certified.Graded

open scoped Polynomial BigOperators

noncomputable section

variable {K : Type*} [CommSemiring K] {ι : Type*} [Fintype ι]

def weightedStageMoment (x b : ι → K) : K[X] →ₗ[K] K :=
  ∑ t, b t • (Polynomial.aeval (x t)).toLinearMap

@[simp] theorem weightedStageMoment_apply (x b : ι → K) (Q : K[X]) :
    weightedStageMoment x b Q = ∑ t, b t * Q.eval (x t) := by
  simp only [weightedStageMoment, LinearMap.sum_apply, LinearMap.smul_apply,
    AlgHom.toLinearMap_apply, Polynomial.coe_aeval_eq_eval, smul_eq_mul]

end
end RKResearch.Certified.Graded
