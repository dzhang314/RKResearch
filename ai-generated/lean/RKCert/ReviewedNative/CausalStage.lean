module

public import RKCert.ReviewedNative.GradedColumns
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic.Ring
public import Mathlib.Data.Fin.Rev
public import Mathlib.Tactic.FieldSimp

@[expose] public section

/-! # Native strict triangularity forces defect growth

A chronological first-coordinate argument applies both to `A` and to `Aᵀ`
in reversed order. No diagonal entry is required to be nonzero. Unlike a
spectral-projection proof, no interpolation polynomial or positive-definite
inner product is used.
-/

namespace RKResearch.Certified.Graded

variable {K : Type*} [Field K] {s : ℕ}

/-- A linear operator depends only on strictly earlier coordinates, in a
specified order. This formulation also covers backward rows. -/
def Causal (ord : Fin s ≃ Fin s) (N : (Fin s→K) →ₗ[K] (Fin s→K)) : Prop :=
  ∀ (i : Fin s) (v : (Fin s→K)), (∀ j, (ord j).val < (ord i).val → v j = 0) → N v i = 0

open scoped Matrix

theorem causal_mat {A : Matrix (Fin s) (Fin s) K} (ha : ∀ i j, i≤j→A i j=0) :
    Causal (Equiv.refl _) (mat A) := by
  intro i v h
  simp only [mat_apply,Matrix.mulVec,dotProduct]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : i.val ≤ j.val
  · rw [ha i j hj, zero_mul]
  · rw [h j (Nat.lt_of_not_ge hj), mul_zero]

theorem causal_transpose {A : Matrix (Fin s) (Fin s) K} (ha : ∀ i j, i≤j→A i j=0) :
    Causal Fin.revPerm (mat A.transpose) := by
  intro i v h
  simp only [mat_apply,Matrix.mulVec,dotProduct,Matrix.transpose_apply]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : j.val ≤ i.val
  · rw [ha j i hj, zero_mul]
  · have ht : j.rev < i.rev := Fin.rev_lt_rev.mpr (Nat.lt_of_not_ge hj)
    rw [h j ht, mul_zero]

/-- Once an invariant subspace contains the quadratic primitive defect, it
must also contain `Yv`. The multiplier 2 is kept in the seed and never divided by. -/
theorem mem_of_invariant_seed (ord : Fin s ≃ Fin s) (N : (Fin s→K) →ₗ[K] (Fin s→K))
    (hc : Causal ord N) (y v : (Fin s→K)) (U : Submodule K ((Fin s→K)))
    (hN : ∀ x ∈ U, N x ∈ U) (hD : ∀ x ∈ U, diag y x ∈ U)
    (hs : (2 : K) • N (diag y v) - diag y (diag y v) ∈ U) : diag y v ∈ U := by
  let z := diag y v
  have go (m : ℕ) : ∃ u ∈ U, (∀ i, (ord i).val < m → u i = z i) ∧
      (∀ i, y i = 0 → u i = 0) := by
    induction m with
    | zero => exact ⟨0, U.zero_mem, fun _ h => False.elim (Nat.not_lt_zero _ h), by simp⟩
    | succ m ih =>
      obtain ⟨u, hu, hprev, hzero⟩ := ih
      by_cases hm : m < s
      · let i := ord.symm ⟨m,hm⟩
        have hii : (ord i).val = m := by simp [i]
        let e := z-u
        let r := diag y (diag y e - (2:K) • N e)
        have hr : r ∈ U := by
          apply hD
          have eqn : diag y e - (2:K) • N e =
              -( (2:K) • N z - diag y z ) - diag y u + (2:K) • N u := by
            simp only [e, map_sub]
            ext j
            simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
            ring
          rw [eqn]
          exact U.add_mem (U.sub_mem (U.neg_mem hs) (hD _ hu)) (U.smul_mem _ (hN _ hu))
        have he (j : Fin s) (hj : (ord j).val < m) : e j = 0 := by
          change z j-u j=0
          rw [hprev j hj, sub_self]
        have hNpre (j : Fin s) (hj : (ord j).val ≤ m) : N e j=0 :=
          hc j e (fun k hk => he k (lt_of_lt_of_le hk hj))
        have hrpre (j : Fin s) (hj : (ord j).val < m) : r j=0 := by
          change y j*(y j*e j-2*N e j)=0
          rw [he j hj, hNpre j hj.le]; ring
        let a := (y i*y i)⁻¹
        refine ⟨u + a • r, U.add_mem hu (U.smul_mem _ hr), ?_, ?_⟩
        · intro j hj
          by_cases hp : (ord j).val < m
          · change u j+a*r j=z j
            rw [hrpre j hp, mul_zero, add_zero, hprev j hp]
          · have hji : j=i := ord.injective (Fin.ext (by omega))
            subst j
            change u i+a*(y i*(y i*e i-2*N e i))=z i
            rw [hNpre i hii.le, mul_zero, sub_zero]
            by_cases hy : y i = 0
            · simp [hy, z, hzero i hy]
            · change u i + (y i*y i)⁻¹ * (y i*(y i*(z i-u i)))=z i
              field_simp
              ring
        · intro j hy
          change u j+a*(y j*(y j*e j-2*N e j))=0
          rw [hzero j hy, hy]; ring
      · exact ⟨u, hu, fun j _ => hprev j (lt_of_lt_of_le (ord j).isLt (Nat.le_of_not_gt hm)), hzero⟩
  obtain ⟨u,hu,hh,_⟩ := go s
  have hu' : u=z := funext fun i => hh i (ord i).isLt
  change z ∈ U
  rwa [← hu']

/-- The first nontrivial level is the span of the seed. Each further level
adds its images under both distinguished operators. -/
noncomputable def orbit (N D : (Fin s→K) →ₗ[K] (Fin s→K)) (q : (Fin s→K)) :
    ℕ → Submodule K ((Fin s→K))
  | 0 => ⊥
  | k+1 =>
    let U := orbit N D q k
    U ⊔ U.map N ⊔ U.map D ⊔ Submodule.span K {q}

theorem orbit_le_succ (N D : (Fin s→K) →ₗ[K] (Fin s→K)) (q : (Fin s→K)) (n : ℕ) :
    orbit N D q n ≤ orbit N D q (n+1) := le_sup_left.trans (le_sup_left.trans le_sup_left)

theorem orbit_rank (ord : Fin s ≃ Fin s) (N : (Fin s→K) →ₗ[K] (Fin s→K))
    (hc : Causal ord N) (y v : (Fin s→K)) (n : ℕ)
    (hout : diag y v ∉ orbit N (diag y) ((2:K) • N (diag y v) - diag y (diag y v)) n) :
    n ≤ Module.finrank K (orbit N (diag y) ((2:K) • N (diag y v) - diag y (diag y v)) n) := by
  let q := (2:K) • N (diag y v) - diag y (diag y v)
  let W := orbit N (diag y) q
  change diag y v ∉ W n at hout
  change n ≤ Module.finrank K (W n)
  induction n with
  | zero => omega
  | succ n ih =>
    have hl : W n ≤ W (n+1) := orbit_le_succ _ _ _ _
    have hr := ih (fun h => hout (hl h))
    have hlt : W n < W (n+1) := by
      refine lt_of_le_of_ne hl ?_
      intro eqn
      apply hout
      apply hl
      have hn (x) (hx : x∈W n) : N x ∈ W n := by
        rw [eqn]
        exact (le_sup_right.trans (le_sup_left.trans le_sup_left) : (W n).map N ≤ W (n+1))
          (Submodule.mem_map_of_mem hx)
      exact mem_of_invariant_seed ord N hc y v (W n) hn (by
        intro x hx; rw [eqn]; exact (le_sup_right.trans le_sup_left : (W n).map (diag y) ≤ W (n+1))
          (Submodule.mem_map_of_mem hx)) (by
        rw [eqn]; exact (le_sup_right : Submodule.span K {q} ≤ W (n+1)) (Submodule.subset_span (Set.mem_singleton q)))
    exact Nat.succ_le_of_lt (lt_of_le_of_lt hr (Submodule.finrank_lt_finrank_of_lt hlt))

end RKResearch.Certified.Graded
