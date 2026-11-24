module

public import RKCert.CausalGrowth

@[expose] public section

/-! # Chronological cancellation for unrestricted triangular tableaux

In the quotient by a common invariant subspace, the two primitive identities
at degrees two and three cannot both hold on a surviving nonzero node. This
proof avoids any choice of quotient basis, spectral projector, or inner product.
The commutator with a diagonal matrix has vanishing chronological diagonal.
-/

namespace RKCert.Paired

variable {K : Type*} [Field K] {s : ℕ}

def CausalDiag (ord : Fin s ≃ Fin s) (N : Vec K s →ₗ[K] Vec K s) (a : Vec K s) : Prop :=
  ∀ (i : Fin s) (v : Vec K s), (∀ j, (ord j).val < (ord i).val → v j = 0) →
    N v i = a i * v i

theorem causalDiag_mat {A : Fin s → Fin s → K}
    (ha : ∀ i j : Fin s, i.val < j.val → A i j = 0) :
    CausalDiag (Equiv.refl _) (mat A) (fun i => A i i) := by
  intro i v h
  change ∑ j, A i j * v j = A i i * v i
  apply Finset.sum_eq_single i
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with hj|hj
    · rw [h j hj, mul_zero]
    · rw [ha i j hj, zero_mul]
  · simp

theorem causalDiag_transpose {A : Fin s → Fin s → K}
    (ha : ∀ i j : Fin s, i.val < j.val → A i j = 0) :
    CausalDiag Fin.revPerm (mat (fun i j => A j i)) (fun i => A i i) := by
  intro i v h
  change ∑ j, A j i * v j = A i i * v i
  apply Finset.sum_eq_single i
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with hj|hj
    · rw [ha j i hj, zero_mul]
    · rw [h j (Fin.rev_lt_rev.mpr hj), mul_zero]
  · simp

/-- If two consecutive primitive defects vanish in an invariant quotient, the
nonzero-node column vanishes there as well, over every field. -/
theorem mem_of_invariant_two_seeds (ord : Fin s ≃ Fin s) (N : Vec K s →ₗ[K] Vec K s)
    (a : Vec K s) (hc : CausalDiag ord N a) (y v : Vec K s) (U : Submodule K (Vec K s))
    (hN : ∀ x ∈ U, N x ∈ U) (hD : ∀ x ∈ U, diag y x ∈ U)
    (h₂ : (2:K) • N (diag y v) - diag y (diag y v) ∈ U)
    (h₃ : (3:K) • N (diag y (diag y v)) - diag y (diag y (diag y v)) ∈ U) :
    diag y v ∈ U := by
  let D := diag y
  let z := D v
  let B := (3:K) • N - D
  let C := (2:K) • N - D
  let T := (2:K) • (B.comp D) - (3:K) • (D.comp C)
  have hT (x) (hx : x ∈ U) : T x ∈ U :=
    U.sub_mem (U.smul_mem _ (U.sub_mem (U.smul_mem _ (hN _ (hD _ hx))) (hD _ (hD _ hx))))
      (U.smul_mem _ (hD _ (U.sub_mem (U.smul_mem _ (hN _ hx)) (hD _ hx))))
  have hz : T z ∈ U := U.sub_mem (U.smul_mem _ h₃) (U.smul_mem _ (hD _ h₂))
  have htri : CausalDiag ord T (fun i => y i ^ 2) := by
    intro i x h
    have hh := hc i x h
    have hD' := hc i (D x) (fun j hj => by change y j * x j = 0; rw [h j hj, mul_zero])
    change N (D x) i = a i * (y i * x i) at hD'
    change 2 * (3 * N (D x) i - y i * (y i * x i)) -
      3 * (y i * (2 * N x i - y i * x i)) = y i ^ 2 * x i
    rw [hh, hD']; ring
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
        let r := D (T e)
        have hr : r ∈ U := hD _ (by change T (z-u) ∈ U; rw [map_sub]; exact U.sub_mem hz (hT u hu))
        have he (j : Fin s) (hj : (ord j).val < m) : e j = 0 := by
          change z j-u j=0; rw [hprev j hj, sub_self]
        have hrr (j : Fin s) (hj : (ord j).val ≤ m) : r j=y j^3 * e j := by
          change y j * (T e j) = _
          rw [htri j e (fun k hk => he k (lt_of_lt_of_le hk hj))]; ring
        let q := (y i^3)⁻¹
        refine ⟨u + q • r, U.add_mem hu (U.smul_mem _ hr), ?_, ?_⟩
        · intro j hj
          by_cases hp : (ord j).val < m
          · change u j + q * r j = z j
            rw [hrr j hp.le, he j hp, mul_zero, mul_zero, add_zero, hprev j hp]
          · have hji : j=i := ord.injective (Fin.ext (by omega))
            subst j
            change u i + (y i^3)⁻¹ * r i = z i
            rw [hrr i hii.le]
            by_cases hy : y i = 0
            · simp [hy, z, D, hzero i hy]
            · rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hy), one_mul]
              change u i + (z i-u i)=z i; abel
        · intro j hy
          change u j + q * (y j * T e j) = 0
          rw [hzero j hy, hy]; ring
      · exact ⟨u, hu, fun j _ => hprev j (lt_of_lt_of_le (ord j).isLt (Nat.le_of_not_gt hm)), hzero⟩
  obtain ⟨u,hu,hh,_⟩ := go s
  have hu' : u=z := funext fun i => hh i (ord i).isLt
  change z ∈ U
  rwa [← hu']

/-- Level 0 contains the linear and quadratic seeds. At each later grade
the cubic seed and both alphabet actions are allowed. -/
noncomputable def twoOrbit (N D : Vec K s →ₗ[K] Vec K s) (q₁ q₂ q₃ : Vec K s) :
    ℕ → Submodule K (Vec K s)
  | 0 => Submodule.span K {q₁} ⊔ Submodule.span K {q₂}
  | n+1 =>
    let U := twoOrbit N D q₁ q₂ q₃ n
    U ⊔ U.map N ⊔ U.map D ⊔ Submodule.span K {q₃}

theorem twoOrbit_le_succ (N D : Vec K s →ₗ[K] Vec K s) (q₁ q₂ q₃ : Vec K s) (n : ℕ) :
    twoOrbit N D q₁ q₂ q₃ n ≤ twoOrbit N D q₁ q₂ q₃ (n+1) :=
  le_sup_left.trans (le_sup_left.trans le_sup_left)

theorem twoOrbit_mono (N D : Vec K s →ₗ[K] Vec K s) (q₁ q₂ q₃ : Vec K s) :
    Monotone (twoOrbit N D q₁ q₂ q₃) := monotone_nat_of_le_succ (twoOrbit_le_succ _ _ _ _ _)

def q₂ (N : Vec K s →ₗ[K] Vec K s) (y v : Vec K s) : Vec K s :=
  (2:K) • N (diag y v) - diag y (diag y v)

def q₃ (N : Vec K s →ₗ[K] Vec K s) (y v : Vec K s) : Vec K s :=
  (3:K) • N (diag y (diag y v)) - diag y (diag y (diag y v))

theorem twoOrbit_rank (ord : Fin s ≃ Fin s) (N : Vec K s →ₗ[K] Vec K s)
    (a : Vec K s) (hc : CausalDiag ord N a) (y v q₁ : Vec K s) (n : ℕ)
    (hout : diag y v ∉ twoOrbit N (diag y) q₁ (q₂ N y v) (q₃ N y v) n) :
    n + Module.finrank K (twoOrbit N (diag y) q₁ (q₂ N y v) (q₃ N y v) 0) ≤
      Module.finrank K (twoOrbit N (diag y) q₁ (q₂ N y v) (q₃ N y v) n) := by
  let W := twoOrbit N (diag y) q₁ (q₂ N y v) (q₃ N y v)
  change diag y v ∉ W n at hout
  change n + Module.finrank K (W 0) ≤ Module.finrank K (W n)
  induction n with
  | zero => simp
  | succ n ih =>
    have hl : W n ≤ W (n+1) := twoOrbit_le_succ _ _ _ _ _ _
    have hr := ih (fun h => hout (hl h))
    have hlt : W n < W (n+1) := by
      refine lt_of_le_of_ne hl ?_
      intro eqn
      apply hout
      apply hl
      apply mem_of_invariant_two_seeds ord N a hc y v (W n)
      · intro x hx; rw [eqn]
        exact (le_sup_right.trans (le_sup_left.trans le_sup_left) : (W n).map N ≤ W (n+1)) (Submodule.mem_map_of_mem hx)
      · intro x hx; rw [eqn]
        exact (le_sup_right.trans le_sup_left : (W n).map (diag y) ≤ W (n+1)) (Submodule.mem_map_of_mem hx)
      · apply twoOrbit_mono _ _ _ _ _ (Nat.zero_le n)
        exact (le_sup_right : Submodule.span K {q₂ N y v} ≤ W 0) (Submodule.subset_span (Set.mem_singleton _))
      · rw [eqn]; exact (le_sup_right : Submodule.span K {q₃ N y v} ≤ W (n+1)) (Submodule.subset_span (Set.mem_singleton _))
    have := Submodule.finrank_lt_finrank_of_lt hlt
    omega

end RKCert.Paired
