module

public import RKCert.ReviewedNative.CoefficientField
public import RKCert.ReviewedNative.ERKUniform
public import RKCert.ReviewedNative.NonsingularDIRKQuadraticFloor
public import RKCert.ReviewedNative.SDIRKOrderSix

public section

/-! # Common-diagonal lower bounds by coefficient specialization

This module uses the reviewed HasOrder.map (ec3d162 or later).
Lean v4.36.0, Mathlib fc4f59e577feb1a4956671bc04ac18aaaf8cd842.
-/

namespace RKResearch

universe u
open scoped Matrix

private theorem strictLower_of_diag_zero {K : Type*} [Zero K] {s : ℕ}
    {A : Matrix (Fin s) (Fin s) K} (ha : A.IsLowerTriangular)
    (hz : ∀ i, A i i = 0) : ∀ i j, i ≤ j → A i j = 0 := by
  intro i j hij
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact hz i
  · exact ha hlt

variable {R : Type u} [CommRing R] {s p : ℕ}
variable {A : Matrix (Fin s) (Fin s) R} {b : Fin s → R} {γ : R}

/-- A nonunit common diagonal can be killed in a residue field, so the
original number of stages satisfies the arbitrary-ring explicit floor. -/
theorem HasOrder.common_diagonal_erk_floor_of_not_isUnit (ho : HasOrder p A b)
    (ha : A.IsLowerTriangular) (hc : ∀ i, A i i = γ) (hu : ¬ IsUnit γ) :
    erkUniformFloor p ≤ s := by
  let J : Ideal R := Ideal.span ({γ} : Set R)
  have hJ : J ≠ ⊤ := by
    intro h
    exact hu (Ideal.span_singleton_eq_top.mp h)
  obtain ⟨I, hI, hJI⟩ := Ideal.exists_le_maximal J hJ
  let := hI
  let := Ideal.Quotient.field I
  let f := Ideal.Quotient.mk I
  have hγJ : γ ∈ J := Ideal.subset_span (by simp)
  have hz : f γ = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (hJI hγJ)
  have hd (i : Fin s) : (A.map f) i i = 0 := (congrArg f (hc i)).trans hz
  exact (RKResearch.HasOrder.map ho f).erk_uniform_floor_le_stages
    (strictLower_of_diag_zero (ha.map f) hd)

/-- A nonnilpotent common diagonal survives in some field, not necessarily
in an arbitrary maximal residue field or in a characteristic-zero field. -/
theorem HasOrder.common_diagonal_quadratic_floor_of_not_isNilpotent
    (ho : HasOrder p A b) (ha : A.IsLowerTriangular) (hc : ∀ i, A i i = γ)
    (hγ : ¬ IsNilpotent γ) (hp : 0 < p) : ((p+1)^2/4+1)/2 ≤ s := by
  let M := Submonoid.powers γ
  have hd : Disjoint ((⊥ : Ideal R) : Set R) (M : Set R) := by
    refine Set.disjoint_left.mpr ?_
    intro x hx hm
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff x γ).mp hm
    exact hγ ⟨n, hn.trans ((Submodule.mem_bot R).mp hx)⟩
  obtain ⟨I, hI, _, hdis⟩ := (⊥ : Ideal R).exists_le_prime_disjoint M hd
  let := hI
  let K := FractionRing (R ⧸ I)
  let f : R →+* K := (algebraMap (R ⧸ I) K).comp (Ideal.Quotient.mk I)
  have hne : f γ ≠ 0 := by
    intro hz
    apply Set.disjoint_left.mp hdis _ (show γ ∈ M from Submonoid.mem_powers γ)
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply IsFractionRing.injective (R ⧸ I) K
    simpa [f] using hz
  have hn (i : Fin s) : (A.map f) i i ≠ 0 := by
    change f (A i i) ≠ 0
    rw [hc i]
    exact hne
  exact (RKResearch.HasOrder.map ho f).nonsingular_quadratic_stage_floor_field
    (ha.map f) hn hp

/-- Every common-diagonal tableau satisfies the smaller of the explicit
and nonsingular floors, even for a zero or nilpotent common diagonal. -/
theorem HasOrder.common_diagonal_stage_floor [Nontrivial R] (ho : HasOrder p A b)
    (ha : A.IsLowerTriangular) (hc : ∀ i, A i i = γ) :
    min (erkUniformFloor p) (((p+1)^2/4+1)/2) ≤ s := by
  by_cases hp : p = 0
  · subst p
    exact (min_le_right _ _).trans (Nat.zero_le s)
  · by_cases hu : IsUnit γ
    · exact (min_le_right _ _).trans (ho.nonsingular_quadratic_stage_floor ha
        (fun i => by simpa only [hc i] using hu) (Nat.pos_of_ne_zero hp))
    · exact (min_le_left _ _).trans (ho.common_diagonal_erk_floor_of_not_isUnit ha hc hu)

/-- In characteristic zero both field branches at order six give seven
stages. No assumption is made on the common ring diagonal. -/
theorem HasOrder.common_diagonal_order_six_stages_charZero [CharZero R]
    (ho : HasOrder 6 A b) (ha : A.IsLowerTriangular) (hc : ∀ i, A i i = γ) :
    7 ≤ s := by
  refine RKCert.ReviewedNative.with_charZero_field (R := R) ?_
  intro K _ _ f
  have ho' := RKResearch.HasOrder.map ho f
  have ha' := ha.map f
  have hc' (i : Fin s) : (A.map f) i i = f γ := congrArg f (hc i)
  by_cases hz : f γ = 0
  · have hs := ho'.erk_uniform_stages_field
      (strictLower_of_diag_zero ha' (fun i => (hc' i).trans hz))
    exact (show 7 ≤ max (6 : ℕ) ((3*6+1)/2-2) by decide).trans hs
  · exact ho'.sdirk_order_six_stages_field ha' hc' hz

end RKResearch
