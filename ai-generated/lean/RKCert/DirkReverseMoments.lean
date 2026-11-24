module

public import RKCert.QuotientGrowth
public import RKCert.ForwardDefects

@[expose] public section

/-! # Reflected tree annihilators for triangular Runge--Kutta tableaux

A reverse row is an honest coordinate vector, paired bilinearly with the
actual stage column. No positivity, division by a weight, or transfer from
a numerical method is used.
-/
namespace RKCert.Paired

variable {K : Type*} [Field K] {s : ℕ}

def rowMap : Vec K s →ₗ[K] Module.Dual K (Vec K s) where
  toFun := row
  map_add' u v := by ext w; simp [add_mul, Finset.sum_add_distrib]
  map_smul' r v := by ext w; simp [Finset.mul_sum, mul_assoc]

theorem row_transp (A : Fin s → Fin s → K) (u v : Vec K s) :
    row (mat (fun i j => A j i) u) v = row u (mat A v) := by
  simp only [row_apply, mat_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  ac_rfl

theorem row_diag (c u v : Vec K s) :
    row (diag c u) v = row u (diag c v) := by
  simp only [row_apply]
  apply Finset.sum_congr rfl; intro j _; change c j * u j * v j=u j*(c j*v j); ring

def reflNode (A : Fin s → Fin s → K) : Vec K s := fun i => 1 - nodes A i

def reflWeight (A : Fin s → Fin s → K) (b : Vec K s) (k : ℕ) : Vec K s :=
  fun i => reflNode A i ^ k * b i

def reflected (A : Fin s → Fin s → K) (b : Vec K s) (k : ℕ) : Vec K s :=
  ((k+1:ℕ):K) • mat (fun i j => A j i) (reflWeight A b k) - reflWeight A b (k+1)

theorem reflected_apply (A : Fin s → Fin s → K) (b x : Vec K s) (k : ℕ) :
    row (reflected A b k) x =
    ((k+1:ℕ):K) * row (reflWeight A b k) (mat A x) - row (reflWeight A b (k+1)) x := by
  change rowMap (((k+1:ℕ):K) • _ - _) x = _
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
  change _ * row (mat _ _) x - _ = _
  rw [row_transp]
  rfl

theorem reflected_0 (A : Fin s → Fin s → K) (b x : Vec K s) :
    row (reflWeight A b 0) x = probe A b 0 x := by
  simp only [reflWeight, reflNode, row_apply, probe]
  apply Finset.sum_congr rfl; intro j _; ring

theorem reflected_1 (A : Fin s → Fin s → K) (b x : Vec K s) :
    row (reflWeight A b 1) x = probe A b 0 x - probe A b 1 x := by
  simp only [reflWeight, reflNode, row_apply, probe, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro j _; ring

theorem reflected_2 (A : Fin s → Fin s → K) (b x : Vec K s) :
    row (reflWeight A b 2) x = probe A b 0 x - 2 * probe A b 1 x + probe A b 2 x := by
  simp only [reflWeight, reflNode, row_apply, probe, Finset.mul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro j _; ring

theorem reflected_3 (A : Fin s → Fin s → K) (b x : Vec K s) :
    row (reflWeight A b 3) x = probe A b 0 x - 3 * probe A b 1 x + 3 * probe A b 2 x - probe A b 3 x := by
  simp only [reflWeight, reflNode, row_apply, probe, Finset.mul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro j _; ring

/-- Tree-level reflected integration-by-parts identities, with the precise
vertex cutoff. The cases use D(1), D(2), and D(3) respectively. -/
theorem reflected_normTree {A : Fin s → Fin s → K} {b : Vec K s} {p : ℕ}
    (ho : HasTreeOrderAtLeast A b p) (t : Tree) (k : ℕ) (hk : k ≤ 2)
    (hpay : t.order+k+1 ≤ p) : row (reflected A b k) (normTree A t) = 0 := by
  let d : K := (t.order:K)
  have hn (r : ℕ) (hr : t.order + r ≤ p) : d+(r:K) ≠ 0 := by
    change (t.order:K)+(r:K) ≠ 0
    rw [← Nat.cast_add]
    exact (isUnit_nat_of_moments (hasMomentsThrough_of_treeOrder ho)
      (Nat.add_pos_left t.order_pos _) hr).ne_zero
  have htst (r : ℕ) (hr : t.order+r ≤ p) :
      probe A b r (normTree A t) = (d+(r:K))⁻¹ := by
    apply mul_left_cancel₀ (hn r hr)
    rw [mul_inv_cancel₀ (hn r hr)]
    simpa [Nat.cast_add, d, add_comm] using probe_normTree ho t r (by omega)
  have hmat (r : ℕ) (hr : t.order+(r+1) ≤ p) :
      probe A b r (mat A (normTree A t)) = (d*(d+((r+1:ℕ):K)))⁻¹ := by
    have hd : d ≠ 0 := by simpa using hn 0 (by omega)
    have hp := mul_ne_zero hd (hn (r+1) hr)
    apply mul_left_cancel₀ hp
    rw [mul_inv_cancel₀ hp]
    have hh := probe_normTree ho (t.attach .leaf) r (by change r+(t.order+1)≤p; omega)
    rw [normTree_unary, map_smul] at hh
    convert hh using 1; simp only [Tree.order, Nat.cast_add, Tree.order, Nat.cast_one,
      smul_eq_mul, d]; ring
  have hk' : k=0 ∨ k=1 ∨ k=2 := by omega
  rcases hk' with rfl|rfl|rfl
  · rw [reflected_apply, reflected_0, reflected_1]
    have h0 := htst 0 (by omega)
    have h1 := htst 1 (by omega)
    have u0 := hmat 0 (by omega)
    have n0 := hn 0 (by omega)
    have n1 := hn 1 (by omega)
    norm_num at h0 h1 u0 n0 n1 ⊢
    rw [u0, h0, h1]
    field_simp
    ring
  · rw [reflected_apply, reflected_1, reflected_2]
    have h0 := htst 0 (by omega)
    have h1 := htst 1 (by omega)
    have h2 := htst 2 (by omega)
    have u0 := hmat 0 (by omega)
    have u1 := hmat 1 (by omega)
    have n0 := hn 0 (by omega)
    have n1 := hn 1 (by omega)
    have n2 := hn 2 (by omega)
    norm_num at h0 h1 h2 u0 u1 n0 n1 n2 ⊢
    rw [u0, u1, h0, h1, h2]
    field_simp
    ring
  · rw [reflected_apply, reflected_2, reflected_3]
    have h0 := htst 0 (by omega)
    have h1 := htst 1 (by omega)
    have h2 := htst 2 (by omega)
    have h3 := htst 3 (by omega)
    have u0 := hmat 0 (by omega)
    have u1 := hmat 1 (by omega)
    have u2 := hmat 2 (by omega)
    have n0 := hn 0 (by omega)
    have n1 := hn 1 (by omega)
    have n2 := hn 2 (by omega)
    have n3 := hn 3 (by omega)
    norm_num at h0 h1 h2 h3 u0 u1 u2 n0 n1 n2 n3 ⊢
    rw [u0, u1, u2, h0, h1, h2, h3]
    field_simp
    ring

theorem reflected_treeSpace {A : Fin s → Fin s → K} {b : Vec K s} {p : ℕ}
    (ho : HasTreeOrderAtLeast A b p) (j k : ℕ) (hk : k≤2) (hpay : j+k+2 ≤ p) :
    treeSpace A j ≤ LinearMap.ker (row (reflected A b k)) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨t, ht, rfl⟩
  change row (reflected A b k) (stageWeight A t) = 0
  have hh := reflected_normTree ho t k hk (by omega)
  change row (reflected A b k) ((t.childDensityProduct:K) • stageWeight A t) = 0 at hh
  rw [map_smul, smul_eq_mul] at hh
  apply (mul_eq_zero.mp hh).resolve_left
  have hd := (IsUnit.of_mul_eq_one _ (ho t (by omega))).ne_zero
  rw [Tree.density, Nat.cast_mul] at hd
  exact (mul_ne_zero_iff.mp hd).2

end RKCert.Paired
