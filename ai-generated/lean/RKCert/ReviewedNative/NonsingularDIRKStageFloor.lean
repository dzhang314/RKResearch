module

public import RKCert.ReviewedNative.GradedSeparation
public import RKCert.ReviewedNative.ChangeCoefficients
public import RKCert.ReviewedNative.Explicit
import Mathlib.Tactic.Ring

@[expose] public section

/-! # The stage floor for nonsingular lower-triangular Runge–Kutta methods

The Volterra commutator sends each *actual* reviewed grade-`j` column into
the homogeneous defect space two grades later. Its triangular diagonal is
`-aᵢᵢ²`, hence it embeds the whole old grade when the diagonal is nonzero.
Independent clock moments give the second summand in the rank recurrence.
No legacy tree, order adapter, sign condition, or characteristic hypothesis.
-/

namespace RKResearch.Certified.Graded
open FiniteRootedTree Module
open scoped FiniteRootedTree Matrix

section Ring

variable {ι R : Type*} [Fintype ι] [CommRing R]
variable {A : Matrix ι ι R} {b : ι → R} {p : ℕ}

/-- The price-two Volterra commutator on reviewed stage columns. -/
def volterra (A : Matrix ι ι R) : (ι → R) →ₗ[R] (ι → R) :=
  (diag (nodes A)).comp (mat A) - (mat A).comp (diag (nodes A)) - (mat A).comp (mat A)

/-- The scaled commutator is a sum of differences of *equal-order* native trees.
Its scalar factors are all units supplied by the achieved order itself. -/
theorem volterra_treeSpace (ho : HasOrder A b p) (j : ℕ) (paid : j+2 ≤ p) :
    treeSpace A j ≤ (zeroSpace A (j+2)).comap (volterra A) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨t, ht, rfl⟩
  let d : R := ((t.order : ℕ) : R)
  let Z := zeroSpace A (j+2)
  let t₁ := (.leaf ◂ t) ◂ .leaf
  let t₂ := .leaf ◂ (t ◂ .leaf)
  let t₃ := .leaf ◂ (.leaf ◂ t)
  have eo₁ : t₁.order = t₃.order := by
    apply PNat.eq
    simp only [t₁, t₃, order, PNat.add_coe, PNat.one_coe]
    omega
  have eo₂ : t₂.order = t₃.order := by
    apply PNat.eq
    simp only [t₂, t₃, order, PNat.add_coe, PNat.one_coe]
    omega
  have h₃ : (t₃.order : ℕ) ≤ j+2+1 := by
    simp only [t₃, order, PNat.add_coe, PNat.one_coe]
    omega
  have e₁ := normDiff_mem (j := j+2) A t₁ t₃ eo₁ (eo₁.symm ▸ h₃)
  have e₂ := normDiff_mem (j := j+2) A t₂ t₃ eo₂ (eo₂.symm ▸ h₃)
  have identity : (d*(d+1)) • volterra A (normTree A t) =
      (d+1) • (normTree A t₁ - normTree A t₃) - d • (normTree A t₂ - normTree A t₃) := by
    simp only [t₁, t₂, t₃, normTree_clock, normTree_unary, order, PNat.add_coe,
      PNat.one_coe, Nat.cast_add, Nat.cast_one, map_smul, volterra, LinearMap.sub_apply,
      LinearMap.comp_apply]
    ext i
    simp only [d, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  have hd : IsUnit d := ho.natCast_isUnit t.order.pos (by omega)
  have hd' : IsUnit (d+1) := by
    simpa only [d, Nat.cast_add, Nat.cast_one] using
      (ho.natCast_isUnit (n := (t.order:ℕ)+1) (by omega) (by omega))
  have hw : volterra A (normTree A t) ∈ Z := by
    apply (Z.smul_mem_iff_of_isUnit (hd.mul hd')).mp
    rw [identity]
    exact Z.sub_mem (Z.smul_mem _ e₁) (Z.smul_mem _ e₂)
  rw [normTree, map_smul] at hw
  exact (Z.smul_mem_iff_of_isUnit (forestFactorial_isUnit ho t (by omega))).mp hw

end Ring

section Field

variable {K : Type*} [Field K] {s p : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}

theorem volterra_pivot (ha : A.IsLowerTriangular) (i : Fin s) (v : Fin s → K)
    (hv : ∀ j, j < i → v j = 0) : volterra A v i = -(A i i)^2 * v i := by
  have hd (j) (hj : j < i) : diag (nodes A) v j = 0 := by simp [hv j hj]
  have hm (j) (hj : j < i) : mat A v j = 0 := by
    rw [mat_apply, lowerTriangular_mulVec_pivot ha j v (fun k hk => hv k (lt_trans hk hj)),
      hv j hj, mul_zero]
  change nodes A i * (A *ᵥ v) i - (A *ᵥ diag (nodes A) v) i - (A *ᵥ mat A v) i = _
  rw [lowerTriangular_mulVec_pivot ha i _ hd, lowerTriangular_mulVec_pivot ha i _ hm,
    mat_apply, lowerTriangular_mulVec_pivot ha i _ hv, diag_apply]
  ring

/-- The diagonal entries may differ. -/
theorem volterra_injective (ha : A.IsLowerTriangular) (hn : ∀ i, A i i ≠ 0) :
    Function.Injective (volterra A) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro v h
  ext i
  induction i using Fin.strong_induction_on with
  | _ i ih =>
    have z := congrFun h i
    rw [volterra_pivot ha i v ih] at z
    simpa [hn i] using z

/-- Paid clock columns and the commutator image are independent inside the native grade. -/
theorem nonsingular_rank_step (ho : HasOrder A b p) (ha : A.IsLowerTriangular)
    (hn : ∀ i, A i i ≠ 0) (j q : ℕ) (grade : q ≤ j+2) (paid : q+j+3 ≤ p) :
    q+1+finrank K (treeSpace A j) ≤ finrank K (treeSpace A (j+2)) := by
  let F := treeSpace A j
  let E := treeSpace A (j+2)
  let f : ((Fin (q+1) → K) × F) →ₗ[K] (Fin s → K) :=
    (coeffEval A q).coprod ((volterra A).comp F.subtype)
  let g : ((Fin (q+1) → K) × F) →ₗ[K] E := f.codRestrict E (fun z =>
    E.add_mem (treeSpace_mono A grade (coeffEval_mem_treeSpace _ _ _))
      (zeroSpace_le_treeSpace _ _ (volterra_treeSpace ho j (by omega) z.2.property)))
  have hg : Function.Injective g := by
    apply (injective_iff_map_eq_zero _).mpr
    intro z hz
    have he : coeffEval A q z.1 + volterra A (z.2 : Fin s → K) = 0 :=
      congrArg (fun w : E => (w : Fin s → K)) hz
    have hu := volterra_treeSpace ho j (by omega) z.2.property
    have h₁ : z.1 = 0 := by
      ext i
      apply moments_detect ho (d := 1) (by decide) (by omega) (fun i l => by omega) z.1 _ i
      intro l
      have obs : probe A b l.val (volterra A (z.2 : Fin s → K)) = 0 :=
        probe_zeroSpace ho (by omega) hu
      have hh := congrArg (probe A b l.val) he
      rwa [map_add, obs, add_zero, probe_coeffEval ho (by omega), map_zero] at hh
    have h₂ : (z.2 : Fin s → K) = 0 := by
      apply (injective_iff_map_eq_zero _).mp (volterra_injective ha hn)
      simpa [h₁] using he
    exact Prod.ext h₁ (Subtype.ext h₂)
  simpa only [Module.finrank_prod, Module.finrank_fin_fun] using
    LinearMap.finrank_le_finrank_of_injective hg

private theorem nonsingular_rank_base (ho : HasOrder A b p) {a q : ℕ}
    (grade : q ≤ a) (paid : q+a+1 ≤ p) : q+1 ≤ finrank K (treeSpace A a) := by
  have eq := treeSpace_rank_eq_of_separation ho (q := q) (by omega) (coeff_separated ho (by omega))
  have mono := Submodule.finrank_mono (treeSpace_mono A grade)
  omega

/-- Sum the independent clock packets on one parity of grades, up to grade `a`. -/
def parityCensus (p : ℕ) : ℕ → ℕ
  | 0 => 1
  | 1 => min 1 (p-2) + 1
  | a+2 => min (a+2) (p-1-(a+2)) + 1 + parityCensus p a

theorem parityCensus_le_finrank (ho : HasOrder A b p) (ha : A.IsLowerTriangular)
    (hn : ∀ i, A i i ≠ 0) :
    ∀ a, a+1 ≤ p → parityCensus p a ≤ finrank K (treeSpace A a)
  | 0, hp => nonsingular_rank_base ho (q := 0) (by decide) hp
  | 1, hp => nonsingular_rank_base ho (Nat.min_le_left ..) (by omega)
  | a+2, hp => by
    have ih := parityCensus_le_finrank ho ha hn a (by omega)
    let q := min (a+2) (p-1-(a+2))
    have step := nonsingular_rank_step ho ha hn a q (Nat.min_le_left ..) (by dsimp [q]; omega)
    change q+1+parityCensus p a ≤ _
    omega

/-- The larger of the two parity counts, valid at every positive order. -/
def nonsingularStageFloor (p : ℕ) : ℕ :=
  max (parityCensus p (p-1)) (parityCensus p (p-2))

theorem nonsingular_stageFloor_field (ho : HasOrder A b p) (ha : A.IsLowerTriangular)
    (hn : ∀ i, A i i ≠ 0) (hp : 0 < p) : nonsingularStageFloor p ≤ s := by
  have count (a : ℕ) (paid : a+1 ≤ p) : parityCensus p a ≤ s := by
    have z := (parityCensus_le_finrank ho ha hn a paid).trans (Submodule.finrank_le _)
    simpa only [Module.finrank_fin_fun] using z
  exact max_le (count _ (by omega)) (count _ (by omega))

end Field
end RKResearch.Certified.Graded

namespace RKResearch

open Certified.Graded

variable {R : Type*} [CommRing R] [Nontrivial R] {s p : ℕ}
variable {A : Matrix (Fin s) (Fin s) R} {b : Fin s → R}

/-- Every individual unit survives passage to the chosen residue field. -/
theorem HasOrder.nonsingular_stageFloor (ho : HasOrder A b p) (ha : A.IsLowerTriangular)
    (hu : ∀ i, IsUnit (A i i)) (hp : 0 < p) : nonsingularStageFloor p ≤ s :=
  ho.unit_diagonal_of_all_fields ha hu (fun _ _ _ _ ht hn h => nonsingular_stageFloor_field h ht hn hp)

/-- Fifth order already needs five stages when *all* diagonal entries are units.
They need not coincide; there are no conditions on the weights. -/
theorem HasOrder.nonsingular_order_five_stages (ho : HasOrder A b 5) (ha : A.IsLowerTriangular)
    (hu : ∀ i, IsUnit (A i i)) : 5 ≤ s := by
  exact ho.nonsingular_stageFloor ha hu (by decide)

/-- Even a shared nonunit (possibly zero or nilpotent) is covered at order five:
its image in a residue field is either zero (explicit) or a unit (nonsingular).
This deliberately does *not* replace arbitrary nonconstant nonzero ring entries by units. -/
theorem HasOrder.common_diagonal_order_five_stages (ho : HasOrder A b 5)
    (ha : A.IsLowerTriangular) {γ : R} (hc : ∀ i, A i i = γ) : 5 ≤ s := by
  obtain ⟨I, hI⟩ := Ideal.exists_maximal R
  let := hI
  let := Ideal.Quotient.field I
  let f := Ideal.Quotient.mk I
  have hf := ho.map_coefficients f
  have ht := ha.map f
  by_cases hz : f γ = 0
  · apply Certified.explicit_order_le_stages (b := f ∘ b) _ hf
    intro i j hij
    rcases eq_or_lt_of_le hij with rfl | lt
    · change f (A i i) = 0
      rwa [hc i]
    · exact ht lt
  · exact nonsingular_stageFloor_field hf ht (fun i => by change f (A i i) ≠ 0; rwa [hc i]) (by decide)

end RKResearch

