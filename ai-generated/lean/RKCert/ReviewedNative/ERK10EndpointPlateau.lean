module

public import RKCert.ReviewedNative.CausalStage
public import Mathlib.LinearAlgebra.Dual.Lemmas

@[expose] public section

/-! A paid rank-three adjoint flag forces the actual first reverse seed to
vanish. The ingress from the word budget to the rank-three flag is separate. -/

namespace RKResearch.Certified.ERK10EndpointPlateau
open Module RKResearch.Certified.Graded
open scoped Matrix

section Marks
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

/-- Defects annihilated by every positive test X Y^k. -/
def silent (M : V →ₗ[F] V) (μ : V →ₗ[F] F) : Submodule F V where
  carrier := {x | ∀ k : ℕ, μ ((M^k) x)=0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy k
    simp [hx k, hy k]
  smul_mem' := by
    intro a x hx k
    simp [hx k]

theorem mem_silent {M : V →ₗ[F] V} {μ : V →ₗ[F] F} {v : V} :
    v ∈ silent M μ ↔ ∀ k : ℕ, μ ((M^k) v)=0 := Iff.rfl

theorem silent_le_ker (M : V →ₗ[F] V) (μ : V →ₗ[F] F) : silent M μ ≤ μ.ker := by
  intro v hv
  simpa only [LinearMap.mem_ker, pow_zero, Module.End.one_eq_id, LinearMap.id_apply]
    using (mem_silent.mp hv) 0

theorem mark_silent {M : V →ₗ[F] V} {μ : V →ₗ[F] F} {v : V}
    (hv : v ∈ silent M μ) : M v ∈ silent M μ := by
  apply mem_silent.mpr
  intro k
  simpa only [pow_succ, Module.End.mul_eq_comp, LinearMap.comp_apply]
    using (mem_silent.mp hv) (k+1)

theorem mark_invariant_le_silent {M : V →ₗ[F] V} {μ : V →ₗ[F] F}
    {U : Submodule F V} (hk : U ≤ μ.ker)
    (hm : ∀ v ∈ U, M v ∈ U) : U ≤ silent M μ := by
  intro v hv
  apply mem_silent.mpr
  intro k
  refine LinearMap.mem_ker.mp (hk ?_)
  induction k with
  | zero => simpa only [pow_zero, Module.End.one_eq_id, LinearMap.id_apply] using hv
  | succ k ih =>
    rw [pow_succ', Module.End.mul_eq_comp, LinearMap.comp_apply]
    exact hm _ ih

/-- If grade j has a nonsilent vector then the remaining mark inclusions
each cost another dimension modulo the silent subspace. -/
theorem escapedFlagCost [FiniteDimensional F V]
    (M : V →ₗ[F] V) (μ : V →ₗ[F] F)
    (D : ℕ → Submodule F V) (monoD : Monotone D)
    (mk : ∀ j < 4, ∀ v ∈ D j, M v ∈ D (j+1))
    (ker4 : D 4 ≤ μ.ker) {j : ℕ} (j4 : j ≤ 4)
    (leak : ¬ D j ≤ silent M μ) (P : Submodule F V)
    (part : P ≤ D 4 ⊓ silent M μ) :
    finrank F P + (5-j) ≤ finrank F (D 4) := by
  let S := silent M μ
  let W (k : ℕ) := D k ⊔ S
  have kerW (k : ℕ) (h : k ≤ 4) : W k ≤ μ.ker :=
    sup_le ((monoD h).trans ker4) (silent_le_ker M μ)
  have init : S < W j := by
    refine lt_of_le_of_ne le_sup_right ?_
    intro eq
    apply leak
    exact (show D j ≤ W j from le_sup_left).trans eq.ge
  have strict (k : ℕ) (kj : j ≤ k) (k4 : k < 4) : W k < W (k+1) := by
    refine lt_of_le_of_ne (sup_le_sup_right (monoD (Nat.le_succ k)) S) ?_
    intro eq
    have inv (v : V) (hv : v∈W k) : M v ∈ W k := by
      change v ∈ D k ⊔ S at hv
      obtain ⟨a, ha, b, hb, same⟩ := Submodule.mem_sup.mp hv
      rw [←same, map_add, eq]
      exact (W (k+1)).add_mem
        ((show D (k+1) ≤ W (k+1) from le_sup_left) (mk k k4 a ha))
        ((show S ≤ W (k+1) from le_sup_right) (mark_silent hb))
    have sub := mark_invariant_le_silent (kerW k k4.le) inv
    exact leak ((monoD kj).trans ((show D k ≤ W k from le_sup_left).trans sub))
  have go (n : ℕ) (within : j+n≤4) : finrank F S+n+1 ≤ finrank F (W (j+n)) := by
    induction n with
    | zero =>
      have t := Submodule.finrank_lt_finrank_of_lt init
      simpa only [Nat.add_zero, Nat.succ_le_iff] using t
    | succ n ih =>
      have fromPrev := ih (by omega)
      have sc := Submodule.finrank_lt_finrank_of_lt (strict (j+n) (by omega) (by omega))
      have e : j+n.succ=j+n+1 := by omega
      rw [e]
      omega
  have full := go (4-j) (by omega)
  have e : j+(4-j)=4 := by omega
  rw [e] at full
  have inter := Submodule.finrank_mono part
  have dim := Submodule.finrank_sup_add_finrank_inf_eq (D 4) S
  change finrank F P ≤ finrank F ↥(D 4 ⊓ S) at inter
  change finrank F (W 4) + finrank F ↥(D 4 ⊓ S) = finrank F (D 4) + finrank F S at dim
  omega

/-- Dimension ledger for a five-dimensional nominal block and two
independent forward residual functionals annihilating the observers. -/
theorem rankCapFromObservers [FiniteDimensional F V]
    (D U : Submodule F V) (sep : Disjoint D U) (nominal : 5 ≤ finrank F U)
    (R : Submodule F (Module.Dual F V)) (residuals : 2 ≤ finrank F R)
    (ann : R ≤ (D ⊔ U).dualAnnihilator) (width : finrank F V ≤ 10) :
    finrank F D ≤ 3 := by
  have hJoin := Submodule.finrank_sup_add_finrank_inf_eq D U
  rw [disjoint_iff.mp sep, finrank_bot, Nat.add_zero] at hJoin
  have hDual := Subspace.finrank_add_finrank_dualAnnihilator_eq (D ⊔ U)
  have hRes := Submodule.finrank_mono ann
  omega

end Marks

section Physical
variable {F : Type*} [Field F] {n : ℕ}

abbrev RevOp (F : Type*) [Field F] (n : ℕ) :=
  (Fin n → F) →ₗ[F] (Fin n → F)

/-- Required rank and moment inputs to the adjoint necessity. Every slot
is paid by the literal reverse short-word budget in the five-opening chart. -/
structure RankThreeFlag (N : RevOp F n) (y w : Fin n → F)
    (μ : (Fin n → F) →ₗ[F] F) where
  D : ℕ → Submodule F (Fin n → F)
  mono : Monotone D
  primitive : ∀ j < 4, ∀ v ∈ D j, N v ∈ D (j+1)
  marked : ∀ j < 4, ∀ v ∈ D j, diag y v ∈ D (j+1)
  cap : finrank F (D 4) ≤ 3
  moment : D 4 ≤ μ.ker
  first : N w - diag y w ∈ D 1
  second : (2:F) • N (diag y w) - diag y (diag y w) ∈ D 2
  nominal : μ (diag y w) ≠ 0

theorem firstAdjointExact {N : RevOp F n} {y w : Fin n → F}
    {μ : (Fin n → F) →ₗ[F] F} (L : RankThreeFlag N y w μ)
    (ord : Fin n ≃ Fin n) (causal : Causal ord N) :
    N w = diag y w := by
  apply sub_eq_zero.mp
  by_contra hv
  let M : RevOp F n := diag y
  let S := silent M μ
  have pureOne : L.D 1 ≤ S := by
    by_contra h
    have b := escapedFlagCost M μ L.D L.mono L.marked L.moment
      (j := 1) (by decide) h ⊥ bot_le
    have bound := L.cap
    omega
  have neq (j : ℕ) (j4 : j<4) (j2 : 2 ≤ j+1) (p : L.D j ≤ S) :
      L.D j ≠ L.D (j+1) := by
    intro e
    have hout : diag y w ∉ L.D j := fun h =>
      L.nominal (LinearMap.mem_ker.mp ((silent_le_ker M μ) (p h)))
    apply hout
    apply mem_of_invariant_seed ord N causal y w (L.D j)
    · intro v h
      rw [e]
      exact L.primitive j j4 v h
    · intro v h
      rw [e]
      exact L.marked j j4 v h
    · rw [e]
      exact L.mono j2 L.second
  have one : 1 ≤ finrank F (L.D 1) := by
    have s : (⊥ : Submodule F (Fin n → F)) < L.D 1 := by
      refine lt_of_le_of_ne bot_le ?_
      intro e
      apply hv
      have t : N w - diag y w ∈ (⊥ : Submodule F (Fin n → F)) := e.symm ▸ L.first
      simpa using t
    have b := Submodule.finrank_lt_finrank_of_lt s
    omega
  have pureTwo : L.D 2 ≤ S := by
    by_contra h
    have b := escapedFlagCost M μ L.D L.mono L.marked L.moment
      (j := 2) (by decide) h (L.D 1)
      (le_inf (L.mono (by decide)) pureOne)
    have bound := L.cap
    omega
  have two : 2 ≤ finrank F (L.D 2) := by
    have s : L.D 1 < L.D 2 :=
      lt_of_le_of_ne (L.mono (by decide)) (neq 1 (by decide) (by decide) pureOne)
    have b := Submodule.finrank_lt_finrank_of_lt s
    omega
  have pureThree : L.D 3 ≤ S := by
    by_contra h
    have b := escapedFlagCost M μ L.D L.mono L.marked L.moment
      (j := 3) (by decide) h (L.D 2)
      (le_inf (L.mono (by decide)) pureTwo)
    have bound := L.cap
    omega
  have s : L.D 2 < L.D 3 :=
    lt_of_le_of_ne (L.mono (by decide)) (neq 2 (by decide) (by decide) pureTwo)
  have t : L.D 3 < L.D 4 :=
    lt_of_le_of_ne (L.mono (by decide)) (neq 3 (by decide) (by decide) pureThree)
  have sRank := Submodule.finrank_lt_finrank_of_lt s
  have tRank := Submodule.finrank_lt_finrank_of_lt t
  have bound := L.cap
  omega

theorem firstLiveAtEndpoint {N : RevOp F n} {y w : Fin n → F}
    {μ : (Fin n → F) →ₗ[F] F} (L : RankThreeFlag N y w μ)
    (ord : Fin n ≃ Fin n) (causal : Causal ord N) (i : Fin n) (wi : w i ≠ 0)
    (earlier : ∀ j, (ord j).val < (ord i).val → w j = 0) :
    y i=0 := by
  have h := congrFun (firstAdjointExact L ord causal) i
  rw [causal i w earlier, diag_apply] at h
  by_contra nz
  exact (mul_ne_zero nz wi) h.symm

open scoped BigOperators
/-- Only the first two paid scalar moments are needed to show that the
nominal masked score lies outside the entire pure defect space. -/
theorem paidTargetNonzero (x w : Fin n → F)
    (mom1 : (2:F) * ∑ i, w i*x i = 1)
    (mom2 : (3:F) * ∑ i, w i*(x i)^2 = 1) :
    row x (diag (fun i => 1-x i) w) ≠ 0 := by
  have e : row x (diag (fun i => 1-x i) w) =
      (∑ i, w i*x i)-(∑ i, w i*(x i)^2) := by
    rw [row_apply, dotProduct, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [diag_apply]
    ring
  intro h
  have same := sub_eq_zero.mp (e.symm.trans h)
  rw [same] at mom1
  have t : (∑ i, w i*(x i)^2)=0 := calc
    _ = 3*(∑ i, w i*(x i)^2)-2*(∑ i, w i*(x i)^2) := by ring
    _ = 0 := by rw [mom1, mom2, sub_self]
  rw [t,mul_zero] at mom2
  exact zero_ne_one mom2

end Physical

end RKResearch.Certified.ERK10EndpointPlateau

#print axioms RKResearch.Certified.ERK10EndpointPlateau.rankCapFromObservers
#print axioms RKResearch.Certified.ERK10EndpointPlateau.escapedFlagCost
#print axioms RKResearch.Certified.ERK10EndpointPlateau.firstAdjointExact
#print axioms RKResearch.Certified.ERK10EndpointPlateau.firstLiveAtEndpoint
#print axioms RKResearch.Certified.ERK10EndpointPlateau.paidTargetNonzero
