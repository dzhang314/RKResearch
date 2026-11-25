module

public import RKCert.ReviewedNative.LocalLinearSilentLane

@[expose] public section

/-! # One-clock modes and real axis refinements -/
namespace RKResearch.Certified.Graded.Reverse.LocalLinear

open RKResearch Module Polynomial RKCert.Endpoint RKCert.Endpoint.WeightedClock PhysicalCensus
open scoped Classical Matrix BigOperators
noncomputable section

variable {K : Type*} [Field K] {s : ℕ}
variable {y ξ τ v : Fin s → K} {M : Submodule K (Fin s → K)} {a : K}

private theorem nonzero_coordinate {x : Fin s → K} (n : x ≠ 0) :
    ∃ i, x i ≠ 0 := by
  by_contra! yes
  exact n (funext yes)

/-- A one-clock mode already inside the complete orbit pays the exact
top Lagrange direction at its actual site. -/
theorem weighted_top_of_local_orbit_mode
    (live : v ≠ 0) (off : ∀ i, y i ≠ a → v i = 0)
    (orb : v ∈ completeOrbit y τ) (paid : v ∈ M) :
    ∃ P : K[X], P.natDegree = (weightedSites y τ).card-1 ∧ weightedEval y τ P ∈ M := by
  obtain ⟨i,vi⟩ := nonzero_coordinate live
  have ia : y i = a := by by_contra no; exact vi (off i no)
  obtain ⟨R,rfl⟩ := orb
  have ti : τ i ≠ 0 := by intro z; apply vi; rw [weightedEval_apply,z,mul_zero]
  have rs : R.eval a ≠ 0 := by
    intro z
    apply vi
    rw [weightedEval_apply,ia,z,zero_mul]
  let D := weightedSites y τ
  have atA : a ∈ D := mem_weightedSites.mpr ⟨i,ti,ia⟩
  let P := Lagrange.basis D id a
  have pd : P.natDegree = D.card-1 := Lagrange.natDegree_basis (Set.injOn_id _) atA
  have extract : weightedEval y τ P = (R.eval a)⁻¹ • weightedEval y τ R := by
    funext j
    simp only [weightedEval_apply,Pi.smul_apply,smul_eq_mul]
    by_cases tj : τ j = 0
    · simp [tj]
    by_cases hit : y j = a
    · have pa : P.eval a=1 := Lagrange.eval_basis_self (Set.injOn_id _) atA
      rw [hit,pa,one_mul,←mul_assoc,inv_mul_cancel₀ rs,one_mul]
    · have jD : y j ∈ D := mem_weightedSites.mpr ⟨j,tj,rfl⟩
      have pz : P.eval (y j)=0 := Lagrange.eval_basis_of_ne (v:=id) (Ne.symm hit) jD
      have vz : R.eval (y j)*τ j=0 := by simpa only [weightedEval_apply] using off j hit
      rw [pz,zero_mul,vz,mul_zero]
  exact ⟨P,pd,extract.symm ▸ M.smul_mem _ paid⟩

/-- A silent local mode of the form τ(ξ-δ), at a clock of nonzero
ordinary mass, needs two genuinely different live axis labels. -/
theorem actual_axis_split_of_silent_local_mode (δ : K)
    (live : v ≠ 0) (off : ∀ i, y i ≠ a → v i = 0)
    (fit : ∀ i, y i = a → v i = τ i*(ξ i-δ))
    (silent : (∑ i, v i) = 0) (mass : clockMass y τ a ≠ 0) :
    ∃ i j, τ i ≠ 0 ∧ τ j ≠ 0 ∧ y i = a ∧ y j = a ∧ ξ i ≠ ξ j := by
  obtain ⟨i,vi⟩ := nonzero_coordinate live
  have ia : y i = a := by by_contra no; exact vi (off i no)
  have ti : τ i ≠ 0 := by intro z; exact vi (by rw [fit i ia,z,zero_mul])
  have di : ξ i-δ ≠ 0 := by intro z; exact vi (by rw [fit i ia,z,mul_zero])
  by_contra no
  have uniform (j : Fin s) (tj : τ j ≠ 0) (ja : y j = a) : ξ i = ξ j := by
    by_contra different
    exact no ⟨i,j,ti,tj,ia,ja,different⟩
  have massFit : (∑ j, v j) = (ξ i-δ)*clockMass y τ a := by
    simp only [clockMass,Finset.sum_filter,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases ja : y j = a
    · rw [if_pos ja,fit j ja]
      by_cases tj : τ j=0
      · simp [tj]
      · rw [←uniform j tj ja,mul_comm]
    · rw [if_neg ja,mul_zero,off j ja]
  exact (mul_ne_zero di mass) (massFit.symm.trans silent)

theorem live_weights_of_advance {w : Fin s → K}
    (step : ∀ i, (y i-a)*v i = w i) (off : ∀ i, y i = a → v i = 0) :
    weightedSites y v = weightedSites y w := by
  ext x
  simp only [mem_weightedSites]
  constructor
  · rintro ⟨i,vi,rfl⟩
    have ia : y i ≠ a := fun on => vi (off i on)
    exact ⟨i,by rw [←step i]; exact mul_ne_zero (sub_ne_zero.mpr ia) vi,rfl⟩
  · rintro ⟨i,wi,rfl⟩
    exact ⟨i,fun vi => wi (by rw [←step i,vi,mul_zero]),rfl⟩

end
end RKResearch.Certified.Graded.Reverse.LocalLinear
