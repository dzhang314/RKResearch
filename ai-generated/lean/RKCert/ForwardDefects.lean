module

public import RKCert.CausalGrowth

@[expose] public section

/-! # Same-grade tree differences and forward rank

The normalized columns of trees of the same order have the same scalar
monomial. Their differences span the homogeneous defect filtration. All
annihilation statements below are derived directly from actual order
conditions, not from a postulated exact-polynomial correspondence.
-/

namespace RKCert.Paired

section Ring
variable {R : Type*} [CommRing R] {s : ℕ}

def zeroSpace (A : Fin s → Fin s → R) (n : ℕ) : Submodule R (Vec R s) :=
  Submodule.span R {v | ∃ t u : Tree, t.order = u.order ∧ t.order ≤ n+1 ∧
    v = normTree A t - normTree A u}

theorem normDiff_mem (A : Fin s → Fin s → R) {n : ℕ} (t u : Tree)
    (he : t.order = u.order) (ht : t.order ≤ n+1) :
    normTree A t - normTree A u ∈ zeroSpace A n :=
  Submodule.subset_span ⟨t,u,he,ht,rfl⟩

theorem zeroSpace_mono (A : Fin s → Fin s → R) {j k : ℕ} (hjk : j ≤ k) :
    zeroSpace A j ≤ zeroSpace A k := by
  apply Submodule.span_le.mpr
  rintro _ ⟨t,u,he,ht,rfl⟩
  exact normDiff_mem _ _ _ he (by omega)

theorem zeroSpace_le_treeSpace (A : Fin s → Fin s → R) (n : ℕ) :
    zeroSpace A n ≤ treeSpace A n := by
  apply Submodule.span_le.mpr
  rintro _ ⟨t,u,he,ht,rfl⟩
  exact (treeSpace A n).sub_mem ((treeSpace A n).smul_mem _ (stageWeight_mem_space A t ht))
    ((treeSpace A n).smul_mem _ (stageWeight_mem_space A u (he ▸ ht)))

theorem normTree_unary (A : Fin s → Fin s → R) (t : Tree) :
    normTree A (.attach t .leaf) = (t.order : R) • mat A (normTree A t) := by
  ext i
  simp only [normTree, Tree.childDensityProduct, Nat.cast_mul, Pi.smul_apply,
    smul_eq_mul, stageWeight, mul_one, mat_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ac_rfl

theorem normTree_shift (A : Fin s → Fin s → R) (t : Tree) :
    normTree A (.attach .leaf t) = diag (nodes A) (normTree A t) := by
  ext i
  simp only [normTree, Tree.childDensityProduct, Tree.order, one_mul, Pi.smul_apply,
    smul_eq_mul, stageWeight, mul_one, diag_apply, nodes]
  ac_rfl

theorem diag_zeroSpace (A : Fin s → Fin s → R) (n : ℕ) :
    zeroSpace A n ≤ (zeroSpace A (n+1)).comap (diag (nodes A)) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨t,u,he,ht,rfl⟩
  change diag (nodes A) (normTree A t - normTree A u) ∈ zeroSpace A (n+1)
  rw [map_sub, ← normTree_shift, ← normTree_shift]
  exact normDiff_mem _ _ _ (by simp only [Tree.order,he]) (by change 1+t.order ≤ n+1+1; omega)

theorem probe_zeroSpace {A : Fin s → Fin s → R} {b : Vec R s} {p n k : ℕ}
    (ho : HasTreeOrderAtLeast A b p) (hpay : k+n+1≤p) :
    zeroSpace A n ≤ LinearMap.ker (probe A b k) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨t,u,he,ht,rfl⟩
  change probe A b k (_ - _) = 0
  rw [map_sub, sub_eq_zero]
  have h := probe_normTree ho t k (by omega)
  have h' := probe_normTree ho u k (by omega)
  rw [← he] at h'
  exact (IsUnit.of_mul_eq_one _ h).mul_left_cancel (h.trans h'.symm)

theorem origin_zeroSpace (A : Fin (s+1) → Fin (s+1) → R) (ha : StrictLower A) (n : ℕ) :
    zeroSpace A n ≤ LinearMap.ker (LinearMap.proj 0) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨t,u,he,ht,rfl⟩
  change normTree A t 0 - normTree A u 0 = 0
  rw [normTree_first A ha, normTree_first A ha, sub_eq_zero]
  have hone (w : Tree) : w = .leaf ↔ w.order = 1 := by
    cases w with
    | leaf => simp [Tree.order]
    | attach x y =>
      have := x.order_pos; have := y.order_pos
      simp only [reduceCtorEq, Tree.order, false_iff]; omega
  simp only [hone, he]

/-- Applying the tableau to a defect advances its grade by exactly one.
The inverse of the tree order used in this step is supplied by the moments. -/
theorem mat_zeroSpace {A : Fin s → Fin s → R} {b : Vec R s} {p : ℕ}
    (ho : HasTreeOrderAtLeast A b p) (n : ℕ) (hn : n+1 ≤ p) :
    zeroSpace A n ≤ (zeroSpace A (n+1)).comap (mat A) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨t,u,he,ht,rfl⟩
  change mat A (normTree A t - normTree A u) ∈ zeroSpace A (n+1)
  have hgen := normDiff_mem (n:=n+1) A (t.attach .leaf) (u.attach .leaf)
    (by simp only [Tree.order,he]) (by change t.order+1≤n+1+1; omega)
  rw [normTree_unary, normTree_unary, ← he, ← smul_sub, ← map_sub] at hgen
  have hu := isUnit_nat_of_moments (hasMomentsThrough_of_treeOrder ho) t.order_pos (by omega)
  obtain ⟨a,ha⟩ := hu
  rw [← ha] at hgen
  have hh := (zeroSpace A (n+1)).smul_mem (↑(a⁻¹) : R) hgen
  simpa only [smul_smul, Units.inv_mul, one_smul] using hh

theorem forward_seed_mem (A : Fin s → Fin s → R) :
    (2:R) • mat A (diag (nodes A) 1) - diag (nodes A) (diag (nodes A) 1) ∈
      zeroSpace A 2 := by
  have h := normDiff_mem (n:=2) A ((Tree.bush 1).attach .leaf) (Tree.bush 2)
    (by decide) (by decide)
  rw [normTree_unary, Tree.order_bush, normTree_bush, normTree_bush] at h
  convert h using 1
  ext i
  simp [pow_two]

end Ring

section Field
variable {K : Type*} [Field K] {s : ℕ} {A : Fin s → Fin s → K} {b : Vec K s} {p : ℕ}

/-- The forward quadratic residual and its A/C orbit give one independent
direction at every grade after grade one. No characteristic-zero assumption. -/
theorem zeroSpace_finrank {n : ℕ} (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b p)
    (hn : n+2 ≤ p) : n ≤ Module.finrank K (zeroSpace A (n+1)) := by
  let c := nodes A
  let seed := (2:K) • mat A (diag c 1) - diag c (diag c 1)
  let W := orbit (mat A) (diag c) seed
  have sub (k : ℕ) (hk : k+2 ≤ p) : W k ≤ zeroSpace A (k+1) := by
    induction k with
    | zero => exact bot_le
    | succ k ih =>
      have hh := ih (by omega)
      change W k ⊔ (W k).map _ ⊔ (W k).map _ ⊔ Submodule.span K {seed} ≤ _
      refine sup_le (sup_le (sup_le (hh.trans (zeroSpace_mono A (by omega))) ?_) ?_) ?_
      · exact Submodule.map_le_iff_le_comap.mpr (hh.trans (mat_zeroSpace ho _ (by omega)))
      · exact Submodule.map_le_iff_le_comap.mpr (hh.trans (diag_zeroSpace A _))
      · apply Submodule.span_le.mpr
        rintro x (rfl : x=seed)
        exact (zeroSpace_mono A (by omega : 2≤k+1+1)) (forward_seed_mem _)
  have hzero (x) (hx : x∈W n) : probe A b 0 x = 0 :=
    probe_zeroSpace ho (by omega : 0+(n+1)+1≤p) (sub n hn hx)
  have hnc : diag c 1 ∉ W n := by
    intro hh
    have hm := probe_normTree ho (Tree.bush 1) 0 (by rw [Tree.order_bush]; omega)
    have ht : normTree A (Tree.bush 1) = diag c 1 := by ext i; simp [normTree_bush, c]
    rw [ht, hzero _ hh, mul_zero] at hm
    exact zero_ne_one hm
  exact le_trans (orbit_rank (Equiv.refl _) (mat A) (causal_mat ha) c 1 n hnc)
    (Submodule.finrank_mono (sub n hn))

end Field
end RKCert.Paired
