module

public import RKCert.ReviewedNative.SDIRKSixTerminal
public import RKCert.ReviewedNative.SDIRKSixFront
public import RKCert.ReviewedNative.GradedProducts
public import Mathlib.LinearAlgebra.Dual.Lemmas

@[expose] public section

/-! # The weighted terminal seed at strict SDIRK(6,6) saturation

Two actual rows vanish on the same five-dimensional cubic tree space. The
ordinary finite-dimensional annihilator theorem makes them proportional.
Evaluation on the last physical columns yields the reflected seed formula,
without assuming the other output weights are nonzero.
-/
namespace RKResearch.Certified.Graded.SDIRKSix
open RKResearch FiniteRootedTree
open scoped FiniteRootedTree Matrix

variable {K : Type*} [Field K]
variable {A : Matrix (Fin 6) (Fin 6) K} {b : (Fin 6 → K)} {γ : K}

/-- The weighted seed row is a scalar multiple of the terminal commutator row. -/
theorem weighted_seed_proportional (ho : HasOrder A b 6) (ha : A.IsLowerTriangular)
    (he : ∀i, A i i=γ) (hγ : γ≠0) :
    ∃ μ : K, μ • (probe A b 0).comp (volterra A) = (probe A b 0).comp (diag (seed A)) := by
  let E := treeSpace A 3
  let H := E.dualAnnihilator
  let B := (probe A b 0).comp (volterra A)
  let S := (probe A b 0).comp (diag (seed A))
  have hB : B ∈ H := (E.mem_dualAnnihilator B).mpr
    (fun _ hx => probe_commutator ho (by decide : 0+3+3≤6) hx)
  have hS : S ∈ H := by
    apply (E.mem_dualAnnihilator S).mpr
    intro x hx
    change probe A b 0 (seed A*x)=0
    exact probe_zeroSpace ho (by decide : 0+(2+3)+1≤6)
      (zeroSpace_mul_treeSpace ho (by decide : 3+1≤6) (seed_zero A) hx)
  have hb5 := (order_six_terminal_chronology ho ha he hγ).1
  let w : H := ⟨B,hB⟩
  have hw : w≠0 := by
    intro hz
    have h := congrArg (fun z : H => (z : Module.Dual K ((Fin 6 → K))) (coord 5)) hz
    change probe A b 0 (volterra A (coord 5))=0 at h
    rw [commutator_coord_five ha he,map_smul,probe_coord] at h
    simp [hγ,hb5] at h
  have hd3 := congrArg (fun ls : List ℕ => ls[3]!)
    (order_six_grade_ranks ho ha (fun i => (he i) ▸ hγ))
  change Module.finrank K E=5 at hd3
  have hd := Subspace.finrank_add_finrank_dualAnnihilator_eq E
  change Module.finrank K E + Module.finrank K H = Module.finrank K (Fin 6→K) at hd
  rw [Module.finrank_fin_fun] at hd
  have hdim : Module.finrank K H=1 := by omega
  have hspan : Submodule.span K ({w} : Set H)=⊤ := by
    simpa using (FiniteDimensional.basisSingleton Unit hdim w hw).span_eq
  obtain ⟨μ,hμ⟩ := (Submodule.span_singleton_eq_top_iff K w).mp hspan (⟨S,hS⟩ : H)
  exact ⟨μ,congrArg Subtype.val hμ⟩

/-- The reflected normalized spacing controls the actual last two seed values. -/
theorem order_six_weighted_terminal_seed (ho : HasOrder A b 6) (ha : A.IsLowerTriangular)
    (he : ∀i, A i i=γ) (hγ : γ≠0) :
    seed A 4 = (1+2*((nodes A 5-nodes A 4)/γ)-((nodes A 5-nodes A 4)/γ)^2)*seed A 5 := by
  obtain ⟨hb5,hb4,_,_,hlink⟩ := order_six_terminal_chronology ho ha he hγ
  obtain ⟨μ,hμ⟩ := weighted_seed_proportional ho ha he hγ
  let D := nodes A 5 - nodes A 4
  change b 5*A 5 4=D*b 4 at hlink
  have h5 := LinearMap.congr_fun hμ (coord 5)
  change μ * probe A b 0 (volterra A (coord 5)) = probe A b 0 (diag (seed A) (coord 5)) at h5
  rw [commutator_coord_five ha he,diag_coord] at h5
  simp only [map_smul,smul_eq_mul,probe_coord,pow_zero,mul_one] at h5
  have s5 : -(μ*γ^2)=seed A 5 := by
    apply mul_left_cancel₀ hb5
    linear_combination h5
  have h4 := LinearMap.congr_fun hμ (coord 4)
  change μ * probe A b 0 (volterra A (coord 4)) = probe A b 0 (diag (seed A) (coord 4)) at h4
  rw [commutator_coord_four ha he,diag_coord] at h4
  simp only [map_add,map_smul,smul_eq_mul,probe_coord,pow_zero,mul_one] at h4
  change μ * (-(γ^2)*b 4 + (D-2*γ)*A 5 4*b 5) = seed A 4*b 4 at h4
  have s4 : μ*(-(γ^2)+(D-2*γ)*D)=seed A 4 := by
    apply mul_left_cancel₀ hb4
    linear_combination h4 - μ*(D-2*γ)*hlink
  change seed A 4=(1+2*(D/γ)-(D/γ)^2)*seed A 5
  rw [←s4,←s5]
  field_simp
  ring

end RKResearch.Certified.Graded.SDIRKSix
