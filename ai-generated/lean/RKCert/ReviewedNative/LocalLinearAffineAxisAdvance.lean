module

public import RKCert.ReviewedNative.WeightedClockPaidAdvance
import Mathlib.Tactic.LinearCombination

@[expose] public section

/-! # Affine advances of a genuine weighted axis

An actual nonconstant affine multiplier has a single knot. Division
at that knot gives either a paid one-clock mode or a paid rational
lift; no pointwise division at the knot is assumed. -/
namespace RKResearch.Certified.Graded.Reverse.LocalLinear

open RKResearch Module Polynomial RKCert.Endpoint RKCert.Endpoint.WeightedClock
open scoped Classical Matrix BigOperators
noncomputable section

variable {K : Type*} [Field K] {s : ℕ}

structure LocalSignedHeadMode (y τ ξ : Fin s → K) (M U : Submodule K (Fin s → K))
    (a δ : K) (v : Fin s → K) : Prop where
  live : v ≠ 0
  paid : v ∈ M
  orthogonal : v ∈ annih U
  off : ∀ i, y i ≠ a → v i = 0
  fit : ∀ i, y i = a → v i = τ i*(ξ i-δ)

structure RationalHeadAdvance (y τ : Fin s → K) (M U : Submodule K (Fin s → K))
    (a : K) (v : Fin s → K) : Prop where
  paid : v ∈ M
  orthogonal : v ∈ annih U
  step : ∀ i, (y i-a)*v i = τ i
  atKnot : ∀ i, y i = a → v i = 0

private theorem affine_eval_factor {T : K[X]} (Td : T.natDegree = 1) :
    ∃ a κ : K, κ ≠ 0 ∧ ∀ x, T.eval x = κ*(x-a) := by
  let R := T /ₘ (X-C 0)
  have rd : R.natDegree = 0 := by
    change (T /ₘ (X-C 0)).natDegree = 0
    rw [clock_linear_quotient_degree, Td]
  let κ := R.coeff 0
  have eqR : R = C κ := eq_C_of_natDegree_eq_zero rd
  have form : C (T.eval 0) + X*C κ = T := by
    have s := clock_linear_quotient_identity T (0 : K)
    change C (T.eval 0) + (X-C 0)*R = T at s
    simpa only [eqR, map_zero, sub_zero] using s
  have kn : κ ≠ 0 := by
    intro zero
    have eq : T = C (T.eval 0) := by
      simpa only [zero, map_zero, mul_zero, add_zero] using form.symm
    rw [eq, natDegree_C] at Td
    exact Nat.zero_ne_one Td
  let a := -T.eval 0/κ
  refine ⟨a,κ,kn,fun x => ?_⟩
  have ev := congrArg (fun P : K[X] => P.eval x) form
  simp only [eval_add,eval_C,eval_mul,eval_X] at ev
  rw [←ev]
  dsimp only [a]
  field_simp [kn]
  <;> ring

/-- The affine alternative strictly accounts for every case without
inventing a high-degree profile. The constant case returns exactly the
first forbidden degree; in the nonconstant case the destroyed low
quotient is explicitly paid and orthogonal. -/
theorem affine_weighted_axis_advance {y τ ξ : Fin s → K} {M U : Submodule K (Fin s → K)}
    {T Q : K[X]} {d : ℕ}
    (Tn : T ≠ 0) (Td : T.natDegree ≤ 1) (Qd : Q.natDegree ≤ d)
    (relation : ∀ i, T.eval (y i)*(τ i*ξ i) = Q.eval (y i)*τ i)
    (small : ∀ R : K[X], R.natDegree ≤ d-1 →
      τ*ξ ≠ weightedEval y τ R)
    (axisPaid : τ*ξ ∈ M) (axisOrth : τ*ξ ∈ annih U)
    (lower : ∀ R : K[X], R.natDegree ≤ d-1 →
      weightedEval y τ R ∈ M ∧ weightedEval y τ R ∈ annih U) :
    (∃ R : K[X], R.natDegree = d ∧ τ*ξ = weightedEval y τ R) ∨
      (∃ a δ v, LocalSignedHeadMode y τ ξ M U a δ v) ∨
      (∃ a v, RationalHeadAdvance y τ M U a v) := by
  by_cases isConstant : T.natDegree = 0
  · let κ := T.coeff 0
    have te : T = C κ := eq_C_of_natDegree_eq_zero isConstant
    have kn : κ ≠ 0 := fun zero => Tn (by rw [te,zero,map_zero])
    let R := C κ⁻¹ * Q
    have rd : R.natDegree ≤ d := by
      change (C κ⁻¹*Q).natDegree ≤ d
      exact (natDegree_C_mul_le _ _).trans Qd
    have form : τ*ξ = weightedEval y τ R := by
      funext i
      have eq := relation i
      rw [te,eval_C] at eq
      rw [Pi.mul_apply, weightedEval_apply]
      change τ i*ξ i = (C κ⁻¹*Q).eval (y i)*τ i
      rw [eval_mul,eval_C,mul_assoc,←eq,←mul_assoc,inv_mul_cancel₀ kn,one_mul]
    exact Or.inl ⟨R, by by_contra! below; exact small R (by omega) form, form⟩
  have linear : T.natDegree = 1 := by omega
  obtain ⟨a,κ,kn,te⟩ := affine_eval_factor linear
  let V := C κ⁻¹*Q
  have vd : V.natDegree ≤ d := (natDegree_C_mul_le _ _).trans Qd
  let R := V /ₘ (X-C a)
  have rd : R.natDegree ≤ d-1 := by
    change (V /ₘ (X-C a)).natDegree ≤ d-1
    rw [clock_linear_quotient_degree]
    omega
  let v := τ*ξ-weightedEval y τ R
  have vn : v ≠ 0 := fun zero => small R rd (sub_eq_zero.mp zero)
  have vp : v ∈ M := M.sub_mem axisPaid (lower R rd).1
  have vo : v ∈ annih U := (annih U).sub_mem axisOrth (lower R rd).2
  have fit (i : Fin s) : v i = τ i*(ξ i-R.eval (y i)) := by
    simp only [v,Pi.sub_apply,Pi.mul_apply,weightedEval_apply]
    ring
  have shift (i : Fin s) : (y i-a)*v i = V.eval a*τ i := by
    have rew := relation i
    rw [te] at rew
    have normalized : (y i-a)*(τ i*ξ i) = V.eval (y i)*τ i := by
      apply mul_left_cancel₀ kn
      change κ*((y i-a)*(τ i*ξ i)) = κ*((C κ⁻¹*Q).eval (y i)*τ i)
      simp only [eval_mul,eval_C]
      calc
        κ*((y i-a)*(τ i*ξ i)) = Q.eval (y i)*τ i := by
          rw [←mul_assoc,rew]
        _ = κ*((κ⁻¹*Q.eval (y i))*τ i) := by
          rw [←mul_assoc,←mul_assoc,mul_inv_cancel₀ kn,one_mul]
    have div := congrArg (fun P : K[X] => P.eval (y i)) (clock_linear_quotient_identity V a)
    change (C (V.eval a)+(X-C a)*R).eval (y i) = V.eval (y i) at div
    simp only [eval_add,eval_C,eval_mul,eval_X,eval_sub] at div
    rw [fit i]
    linear_combination normalized - τ i * div
  by_cases zero : V.eval a = 0
  · refine Or.inr (Or.inl ⟨a,R.eval a,v,vn,vp,vo,?_,?_⟩)
    · intro i off
      have mode := shift i
      rw [zero,zero_mul] at mode
      exact (mul_eq_zero.mp mode).resolve_left (sub_ne_zero.mpr off)
    · intro i on
      rw [fit i,on]
  let w := (V.eval a)⁻¹ • v
  refine Or.inr (Or.inr ⟨a,w,M.smul_mem _ vp,(annih U).smul_mem _ vo,?_,?_⟩)
  · intro i
    change (y i-a)*((V.eval a)⁻¹*v i) = τ i
    calc
      _ = (V.eval a)⁻¹*((y i-a)*v i) := by ring
      _ = τ i := by rw [shift i,←mul_assoc,inv_mul_cancel₀ zero,one_mul]
  · intro i on
    have zi := shift i
    rw [on,sub_self,zero_mul] at zi
    have ti := (mul_eq_zero.mp zi.symm).resolve_left zero
    change (V.eval a)⁻¹*v i = 0
    rw [fit i,ti,zero_mul,mul_zero]

end
end RKResearch.Certified.Graded.Reverse.LocalLinear
