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

section Stable

variable {F M : Type*} [Field F] [AddCommGroup M] [Module F M] [FiniteDimensional F M]

/-- Injectivity only on P is sufficient, even if the ambient map is singular.
The RK element z and its comparison direction both live in P. -/
private theorem dirk_stable_preimage (L : M →ₗ[F] M) (P U : Submodule F M)
    (hP : P ≤ P.comap L) (hU : U ≤ U.comap L)
    (hinj : ∀ x ∈ P, L x=0 → x=0) (z : M) (hz : z∈P) (hw : L z∈U) : z∈U := by
  let V := P ⊓ U
  have hj : Set.InjOn L P := fun x hx y hy he =>
    sub_eq_zero.mp (hinj (x-y) (P.sub_mem hx hy) (by rw [map_sub,he,sub_self]))
  have hV (x) (hx : x∈V) : L x ∈ V := ⟨hP hx.1,hU hx.2⟩
  obtain ⟨x,hx,he⟩ := (LinearMap.injOn_iff_surjOn hV).mp
    (hj.mono (show (V:Set M) ⊆ P from inf_le_left)) (show L z∈V from ⟨hP hz,hw⟩)
  exact hj hx.1 hz he ▸ hx.2

end Stable


/-- A triangular map whose diagonal is a nonzero power of y has no kernel
on columns supported on nonzero y. This is the only coordinate induction. -/
private theorem dirk_supported_kernel (ord : Fin s ≃ Fin s) (T : Vec K s →ₗ[K] Vec K s)
    (y : Vec K s) (hT : CausalDiag ord T (fun i => y i^3))
    (x : Vec K s) (hs : ∀ i, y i=0 → x i=0) (hx : T x=0) : x=0 := by
  funext i
  induction hm : (ord i).val using Nat.strong_induction_on generalizing i with
  | _ n ih =>
    have hh := hT i x (fun j hj => ih (ord j).val (by omega) j rfl)
    have hz : y i^3*x i=0 := hh.symm.trans (congrFun hx i)
    by_cases hy : y i=0
    · exact hs i hy
    · exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ hy)

/-- If two consecutive primitive defects vanish in an invariant quotient, the
nonzero-node column vanishes there as well, over every field. -/
theorem mem_of_invariant_two_seeds (ord : Fin s ≃ Fin s) (N : Vec K s →ₗ[K] Vec K s)
    (a : Vec K s) (hc : CausalDiag ord N a) (y v : Vec K s) (U : Submodule K (Vec K s))
    (hN : ∀ x ∈ U, N x ∈ U) (hD : ∀ x ∈ U, diag y x ∈ U)
    (h₂ : (2:K) • N (diag y v) - diag y (diag y v) ∈ U)
    (h₃ : (3:K) • N (diag y (diag y v)) - diag y (diag y (diag y v)) ∈ U) :
    diag y v ∈ U := by
  let D := Paired.diag y
  let z := D v
  let B := (3:K) • N - D
  let C := (2:K) • N - D
  let L := D.comp ((2:K) • (B.comp D) - (3:K) • (D.comp C))
  let P : Submodule K (Vec K s) := Submodule.pi {i | y i=0} (fun _ => ⊥)
  have hS (x : Vec K s) : D x ∈ P := by
    intro i (hi : y i=0); change y i*x i=0; rw [hi,zero_mul]
  have hU (x) (hx : x∈U) : L x ∈ U := hD _
    (U.sub_mem (U.smul_mem _ (U.sub_mem (U.smul_mem _ (hN _ (hD _ hx))) (hD _ (hD _ hx))))
      (U.smul_mem _ (hD _ (U.sub_mem (U.smul_mem _ (hN _ hx)) (hD _ hx)))))
  have htri : CausalDiag ord L (fun i => y i^3) := by
    intro i x h
    have hh := hc i x h
    have hD' := hc i (D x) (fun j hj => by change y j*x j=0; rw [h j hj,mul_zero])
    change N (D x) i=a i*(y i*x i) at hD'
    change y i * (2*(3*N (D x) i-y i*(y i*x i)) - 3*(y i*(2*N x i-y i*x i)))=y i^3*x i
    rw [hD',hh]; ring
  apply dirk_stable_preimage L P U (fun _ _ => hS _) (fun _ => hU _)
    (fun x hx => dirk_supported_kernel ord L y htri x hx) z (hS _)
  exact hD _ (U.sub_mem (U.smul_mem _ h₃) (U.smul_mem _ (hD _ h₂)))

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
