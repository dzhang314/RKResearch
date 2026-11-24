module

public import RKCert.CausalGrowth
public import RKCert.StageBound
public import Mathlib.Tactic.LinearCombination

@[expose] public section

/-! # Backward RK defects over arbitrary fields

Only the first two backward residuals are needed. We propagate them under
the tableau transpose and the reflected node diagonal. The pairing here is
bilinear, including over finite fields, and requires no sign on the weights.
-/

namespace RKCert.Paired
open Module

variable {K : Type*} [Field K] {s : ℕ}

/-- Row vectors as linear functionals on the stage space. -/
def rowL : Vec K s →ₗ[K] Module.Dual K (Vec K s) where
  toFun := row
  map_add' u v := by ext x; simp [row_apply, add_mul, Finset.sum_add_distrib]
  map_smul' r u := by ext x; simp [row_apply, mul_assoc, Finset.mul_sum]

@[simp] theorem rowL_apply (u v : Vec K s) : rowL u v = row u v := rfl

theorem rowL_inj : Function.Injective (rowL (K:=K) (s:=s)) := by
  intro x y h
  ext i
  have hi := LinearMap.congr_fun h (Pi.single i (1:K))
  simpa [row_apply, Pi.single_apply] using hi

/-- Ordinary annihilating stage rows, not a Hermitian complement. -/
def annih (U : Submodule K (Vec K s)) : Submodule K (Vec K s) :=
  U.dualAnnihilator.comap rowL

theorem mem_annih {U : Submodule K (Vec K s)} {u : Vec K s} :
    u ∈ annih U ↔ ∀ v ∈ U, row u v = 0 := Submodule.mem_dualAnnihilator (rowL u)

theorem finrank_annih_le {U V : Submodule K (Vec K s)} (h : V ≤ annih U) :
    finrank K U + finrank K V ≤ s := by
  have hmap : V.map rowL ≤ U.dualAnnihilator := Submodule.map_le_iff_le_comap.mpr h
  have hdim := Submodule.finrank_mono hmap
  have heq := Subspace.finrank_add_finrank_dualAnnihilator_eq U
  rw [← (Submodule.equivMapOfInjective rowL rowL_inj V).finrank_eq] at hdim
  simpa using (calc
    finrank K U + finrank K V ≤ finrank K U + finrank K U.dualAnnihilator :=
      Nat.add_le_add_left hdim _
    _ = finrank K (Vec K s) := heq)

def mirror (A : Fin s → Fin s → K) : Vec K s := 1 - nodes A

abbrev transMat (A : Fin s → Fin s → K) := mat (fun i j => A j i)

theorem row_flip_mat (A : Fin s → Fin s → K) (w v : Vec K s) :
    row (transMat A w) v = row w (mat A v) := by
  simp only [row_apply, mat_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ac_rfl

theorem row_flip_diag (y w v : Vec K s) :
    row (diag y w) v = row w (diag y v) := by
  simp only [row_apply, diag_apply]
  apply Finset.sum_congr rfl
  intro i _
  ac_rfl

private theorem row_subL (u w v : Vec K s) :
    row (u-w) v = row u v - row w v := congrArg (fun f : Module.Dual K (Vec K s) => f v)
      (rowL.map_sub u w)

private theorem row_smulL (a : K) (u v : Vec K s) :
    row (a • u) v = a * row u v := congrArg (fun f : Module.Dual K (Vec K s) => f v)
      (rowL.map_smul a u)

private theorem row_probe0 (A : Fin s → Fin s → K) (b v : Vec K s) :
    row b v = probe A b 0 v := by simp [probe]

theorem row_mirror (A : Fin s → Fin s → K) (b v : Vec K s) :
    row (diag (mirror A) b) v = probe A b 0 v - probe A b 1 v := by
  simp only [row_apply, probe, diag_apply, mirror, Pi.sub_apply, Pi.one_apply, pow_zero,
    pow_one, mul_one, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem row_mirror2 (A : Fin s → Fin s → K) (b v : Vec K s) :
    row (diag (mirror A) (diag (mirror A) b)) v =
      probe A b 0 v - 2 * probe A b 1 v + probe A b 2 v := by
  simp only [row_apply, probe, diag_apply, mirror, Pi.sub_apply, Pi.one_apply, pow_zero,
    pow_one, mul_one, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Integers in an actual order budget never vanish in the coefficient field. -/
theorem cast_ne_zero_of_budget {A : Fin s → Fin s → K} {b : Vec K s} {p n : ℕ}
    (ho : HasTreeOrderAtLeast A b p) (hn : 0 < n) (hle : n ≤ p) : (n : K) ≠ 0 :=
  (isUnit_nat_of_moments (hasMomentsThrough_of_treeOrder ho) hn hle).ne_zero

theorem child_nonzero {A : Fin s → Fin s → K} {b : Vec K s} {p : ℕ}
    (ho : HasTreeOrderAtLeast A b p) (t : Tree) (ht : t.order ≤ p) :
    (t.childDensityProduct : K) ≠ 0 := by
  have hd := (treeDensity_isUnit_of_moments (hasMomentsThrough_of_treeOrder ho) t ht).ne_zero
  rw [Tree.density, Nat.cast_mul] at hd
  exact (mul_ne_zero_iff.mp hd).2

theorem probe_norm_inv {A : Fin s → Fin s → K} {b : Vec K s} {p : ℕ}
    (ho : HasTreeOrderAtLeast A b p) (t : Tree) (k : ℕ) (hk : k+t.order ≤ p) :
    probe A b k (normTree A t) = ((t.order : K) + k)⁻¹ := by
  have h := probe_normTree ho t k hk
  rw [Nat.cast_add, add_comm (k:K)] at h
  exact inv_eq_of_mul_eq_one_right h |>.symm

theorem mat_norm_extend (A : Fin s → Fin s → K) (t : Tree) :
    (t.order : K) • mat A (normTree A t) = normTree A (.attach t .leaf) := by
  ext i
  simp only [normTree, stageWeight, Tree.childDensityProduct, Nat.cast_mul,
    Pi.smul_apply, smul_eq_mul, mat_apply, mul_one, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ac_rfl

theorem probe_mat_norm_inv {A : Fin s → Fin s → K} {b : Vec K s} {p : ℕ}
    (ho : HasTreeOrderAtLeast A b p) (t : Tree) (k : ℕ) (hk : k+t.order+1 ≤ p) :
    probe A b k (mat A (normTree A t)) =
      ((t.order : K) + 1 + k)⁻¹ / t.order := by
  have hn := cast_ne_zero_of_budget ho t.order_pos (by omega)
  apply (eq_div_iff hn).mpr
  rw [mul_comm, ← smul_eq_mul, ← map_smul, mat_norm_extend]
  simpa only [Tree.order, Nat.cast_add, Nat.cast_one] using
    probe_norm_inv ho (.attach t .leaf) k (by change k+(t.order+1)≤p; omega)

def backSeed1 (A : Fin s → Fin s → K) (b : Vec K s) : Vec K s :=
  transMat A b - diag (mirror A) b

def backSeed2 (A : Fin s → Fin s → K) (b : Vec K s) : Vec K s :=
  (2:K) • transMat A (diag (mirror A) b) - diag (mirror A) (diag (mirror A) b)

private theorem backSeed1_norm {A : Fin s → Fin s → K} {b : Vec K s} {p : ℕ}
    (ho : HasTreeOrderAtLeast A b p) (t : Tree) (ht : t.order+1 ≤ p) :
    row (backSeed1 A b) (normTree A t) = 0 := by
  rw [backSeed1, row_subL, row_flip_mat, row_probe0 A, row_mirror,
    probe_mat_norm_inv ho t 0 (by omega), probe_norm_inv ho t 0 (by omega),
    probe_norm_inv ho t 1 (by omega)]
  have hn := cast_ne_zero_of_budget ho t.order_pos (by omega)
  have hn1 : (t.order : K)+1 ≠ 0 := by
    simpa using cast_ne_zero_of_budget ho (n:=t.order+1) (by omega) ht
  simp only [Nat.cast_zero, Nat.cast_one, add_zero]
  field_simp
  ring

private theorem backSeed2_norm {A : Fin s → Fin s → K} {b : Vec K s} {p : ℕ}
    (ho : HasTreeOrderAtLeast A b p) (t : Tree) (ht : t.order+2 ≤ p) :
    row (backSeed2 A b) (normTree A t) = 0 := by
  rw [backSeed2, row_subL, row_smulL, row_flip_mat, row_mirror, row_mirror2,
    probe_mat_norm_inv ho t 0 (by omega), probe_mat_norm_inv ho t 1 (by omega),
    probe_norm_inv ho t 0 (by omega), probe_norm_inv ho t 1 (by omega), probe_norm_inv ho t 2 (by omega)]
  have hn := cast_ne_zero_of_budget ho t.order_pos (by omega)
  have hn1 : (t.order : K)+1 ≠ 0 := by
    simpa using cast_ne_zero_of_budget ho (n:=t.order+1) (by omega) (by omega)
  have hn2 : (t.order : K)+2 ≠ 0 := by
    simpa using cast_ne_zero_of_budget ho (n:=t.order+2) (by omega) ht
  simp only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, add_zero,
    show (t.order:K)+1+1 = t.order+2 by ring]
  field_simp
  ring

theorem annih_of_norm {A : Fin s → Fin s → K} {b w : Vec K s} {p j : ℕ}
    (ho : HasTreeOrderAtLeast A b p) (hj : j+1≤p)
    (h : ∀ t : Tree, t.order≤j+1 → row w (normTree A t) = 0) :
    w ∈ annih (treeSpace A j) := by
  rw [mem_annih]
  change treeSpace A j ≤ (row w).ker
  apply Submodule.span_le.mpr
  rintro _ ⟨t, ht, rfl⟩
  have hz := h t ht
  rw [normTree, map_smul, smul_eq_mul] at hz
  exact (mul_eq_zero.mp hz).resolve_left (child_nonzero ho t (by omega))

theorem backSeed1_annih {A : Fin s → Fin s → K} {b : Vec K s} {p j : ℕ}
    (ho : HasTreeOrderAtLeast A b p) (hj : j+2 ≤ p) :
    backSeed1 A b ∈ annih (treeSpace A j) :=
  annih_of_norm ho (by omega) (fun t ht => backSeed1_norm ho t (by omega))

theorem backSeed2_annih {A : Fin s → Fin s → K} {b : Vec K s} {p j : ℕ}
    (ho : HasTreeOrderAtLeast A b p) (hj : j+3 ≤ p) :
    backSeed2 A b ∈ annih (treeSpace A j) :=
  annih_of_norm ho (by omega) (fun t ht => backSeed2_norm ho t (by omega))

end RKCert.Paired
