module

public import RKCert.ReviewedNative.ERK10EndpointPlateau

@[expose] public section

namespace RKResearch.Certified.ERK10DirtyPlateauRank
open Module RKResearch.Certified.Graded RKResearch.Certified.ERK10EndpointPlateau

variable {F : Type*} [Field F] {n : ℕ}

/-- Grade four already has at least three defect dimensions, even if no
rank cap and no first primitive seed are assumed. -/
theorem gradeFourFloor (N : RevOp F n) (y w : Fin n → F)
    (μ : (Fin n → F) →ₗ[F] F)
    (ord : Fin n ≃ Fin n) (hc : Causal ord N)
    (D : ℕ → Submodule F (Fin n → F)) (monoD : Monotone D)
    (prim : ∀ j < 4, ∀ v ∈ D j, N v ∈ D (j+1))
    (mark : ∀ j < 4, ∀ v ∈ D j, diag y v ∈ D (j+1))
    (ker4 : D 4 ≤ μ.ker)
    (seed : (2:F) • N (diag y w) - diag y (diag y w) ∈ D 2)
    (target : μ (diag y w)≠0) :
    3 ≤ finrank F (D 4) := by
  by_contra bad
  have cap : finrank F (D 4) ≤ 2 := by omega
  let S := silent (diag y) μ
  have pureTwo : D 2 ≤ S := by
    by_contra leak
    have c := escapedFlagCost (diag y) μ D monoD mark ker4
      (j := 2) (by decide) leak ⊥ bot_le
    omega
  have nz : (2:F) • N (diag y w) - diag y (diag y w) ≠ 0 := by
    intro e
    have stepN (x : Fin n → F) (hx : x ∈ (⊥ : Submodule F (Fin n → F))) :
        N x ∈ (⊥ : Submodule F (Fin n → F)) := by
      have ex : x=0 := by simpa using hx
      simp [ex]
    have stepY (x : Fin n → F) (hx : x ∈ (⊥ : Submodule F (Fin n → F))) :
        diag y x ∈ (⊥ : Submodule F (Fin n → F)) := by
      have ex : x=0 := by simpa using hx
      simp [ex]
    have t := mem_of_invariant_seed ord N hc y w ⊥ stepN stepY (by simp [e])
    have t0 : diag y w=0 := by simpa using t
    exact target (by simp [t0])
  have dimTwo : 1 ≤ finrank F (D 2) := by
    have h : (⊥ : Submodule F (Fin n → F)) < D 2 := by
      refine lt_of_le_of_ne bot_le ?_
      intro e
      have q := (e.symm ▸ seed : (2:F) • N (diag y w) - diag y (diag y w) ∈
        (⊥ : Submodule F (Fin n → F)))
      exact nz (by simpa using q)
    have d := Submodule.finrank_lt_finrank_of_lt h
    omega
  have pureThree : D 3 ≤ S := by
    by_contra leak
    have c := escapedFlagCost (diag y) μ D monoD mark ker4
      (j := 3) (by decide) leak (D 2)
      (le_inf (monoD (by decide)) pureTwo)
    omega
  have noPlateau (j : ℕ) (hj : j<4) (hj2 : 2≤j) (pure : D j ≤ S) :
      D j ≠ D (j+1) := by
    intro e
    have h := mem_of_invariant_seed ord N hc y w (D j)
      (fun x hx => by rw [e]; exact prim j hj x hx)
      (fun x hx => by rw [e]; exact mark j hj x hx)
      (monoD hj2 seed)
    exact target (LinearMap.mem_ker.mp (silent_le_ker (diag y) μ (pure h)))
  have s : D 2 < D 3 :=
    lt_of_le_of_ne (monoD (by decide)) (noPlateau 2 (by decide) (by decide) pureTwo)
  have t : D 3 < D 4 :=
    lt_of_le_of_ne (monoD (by decide)) (noPlateau 3 (by decide) (by decide) pureThree)
  have a := Submodule.finrank_lt_finrank_of_lt s
  have b := Submodule.finrank_lt_finrank_of_lt t
  omega

/-- Width consequence of the true grade-four floor, five independent
nominal columns, and an arbitrary space of paired residual functionals. -/
theorem widthFromResidualRank {V : Type*} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (D U : Submodule F V)
    (sep : Disjoint D U) (defects : 3 ≤ finrank F D) (nominal : 5 ≤ finrank F U)
    (R : Submodule F (Module.Dual F V)) (ann : R ≤ (D ⊔ U).dualAnnihilator) :
    8+finrank F R ≤ finrank F V := by
  have hJoin := Submodule.finrank_sup_add_finrank_inf_eq D U
  rw [disjoint_iff.mp sep, finrank_bot, Nat.add_zero] at hJoin
  have hDual := Subspace.finrank_add_finrank_dualAnnihilator_eq (D ⊔ U)
  have hRes := Submodule.finrank_mono ann
  omega

end RKResearch.Certified.ERK10DirtyPlateauRank

#print axioms RKResearch.Certified.ERK10DirtyPlateauRank.gradeFourFloor
#print axioms RKResearch.Certified.ERK10DirtyPlateauRank.widthFromResidualRank
