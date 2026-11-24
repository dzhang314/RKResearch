module

public import RKCert.ForwardDefects

@[expose] public section

/-! # Rooted-sum products on the actual graded E/F spaces

Identifying the roots of two trees adds their grades. This file proves the
consequent product rules on all elements of the span, rather than just
asserting closure on generators. No sign, characteristic, or field structure
is required.
-/
namespace RKCert.Tree

/-- Join the two roots, retaining the first tree's children followed by the
second tree's children. Commutativity is not asserted for the ordered syntax. -/
def rootSum : Tree → Tree → Tree
  | .leaf, u => u
  | .attach c t, u => .attach c (rootSum t u)

theorem order_rootSum (t u : Tree) : (rootSum t u).order+1 = t.order+u.order := by
  induction t with
  | leaf => simp [rootSum, order, Nat.add_comm]
  | attach c t _ ih => simp only [rootSum, order]; omega

@[simp] theorem childDensityProduct_rootSum (t u : Tree) :
    (rootSum t u).childDensityProduct = t.childDensityProduct * u.childDensityProduct := by
  induction t with
  | leaf => simp [rootSum, childDensityProduct]
  | attach c t _ ih => simp only [rootSum, childDensityProduct, ih]; ac_rfl

end RKCert.Tree

namespace RKCert.Paired

section Semiring
variable {R : Type*} [CommSemiring R] {s : ℕ}

theorem stageWeight_rootSum (A : Fin s → Fin s → R) (t u : Tree) (i : Fin s) :
    stageWeight A (t.rootSum u) i = stageWeight A t i * stageWeight A u i := by
  induction t with
  | leaf => simp [Tree.rootSum, stageWeight]
  | attach c t _ ih => simp only [Tree.rootSum, stageWeight, ih, mul_assoc]

theorem normTree_rootSum (A : Fin s → Fin s → R) (t u : Tree) :
    normTree A (t.rootSum u) = normTree A t * normTree A u := by
  ext i
  simp only [normTree, Pi.smul_apply, smul_eq_mul, Pi.mul_apply,
    Tree.childDensityProduct_rootSum, Nat.cast_mul, stageWeight_rootSum]
  ac_rfl

/-- Pointwise multiplication as a bilinear map. -/
def hadamard : Vec R s →ₗ[R] Vec R s →ₗ[R] Vec R s where
  toFun x := diag x
  map_add' x y := by ext w i; simp [add_mul]
  map_smul' r x := by ext w i; simp [mul_assoc]

theorem hadamard_apply (v w : Vec R s) : hadamard v w = v*w := rfl

theorem treeSpace_mul {A : Fin s → Fin s → R} {m n : ℕ} {v w : Vec R s}
    (hv : v∈treeSpace A m) (hw : w∈treeSpace A n) : v*w ∈ treeSpace A (m+n) := by
  rw [← hadamard_apply]
  apply LinearMap.BilinMap.apply_apply_mem_of_mem_span _ _ _ hadamard _ _ _ hv hw
  rintro _ ⟨t,ht,rfl⟩ _ ⟨u,hu,rfl⟩
  have he : hadamard (stageWeight A t) (stageWeight A u) = stageWeight A (t.rootSum u) :=
    funext fun i => (stageWeight_rootSum A t u i).symm
  rw [he]
  exact stageWeight_mem_space _ _ (by have := Tree.order_rootSum t u; omega)

end Semiring

section Ring
variable {R : Type*} [CommRing R] {s p : ℕ} {A : Fin s → Fin s → R} {b : Vec R s}

private theorem mul_normDiff {m n : ℕ} (t u r : Tree) (he : t.order=u.order)
    (ht : t.order ≤ m+1) (hr : r.order ≤ n+1) :
    (normTree A t - normTree A u)*normTree A r ∈ zeroSpace A (m+n) := by
  rw [sub_mul, ← normTree_rootSum, ← normTree_rootSum]
  have h1 := Tree.order_rootSum t r
  have h2 := Tree.order_rootSum u r
  exact normDiff_mem _ _ _ (by omega) (by omega)

/-- Multiplication of two homogeneous defects consumes the sum of their
grades. This rule does not even require an order condition on the tableau. -/
theorem zeroSpace_mul {m n : ℕ} {v w : Vec R s} (hv : v∈zeroSpace A m)
    (hw : w∈zeroSpace A n) : v*w∈zeroSpace A (m+n) := by
  rw [← hadamard_apply]
  apply LinearMap.BilinMap.apply_apply_mem_of_mem_span _ _ _ hadamard _ _ _ hv hw
  rintro _ ⟨t,u,htu,ht,rfl⟩ _ ⟨r,l,hrl,hr,rfl⟩
  rw [hadamard_apply, mul_sub]
  exact (zeroSpace A (m+n)).sub_mem (mul_normDiff _ _ _ htu ht hr)
    (mul_normDiff _ _ _ htu ht (by omega))

/-- Arbitrary tree partners (not only residuals or monomials) preserve the
defect ideal, with the joint grade. Order pays for the *partner* normalization. -/
theorem zeroSpace_mul_treeSpace (ho : HasTreeOrderAtLeast A b p) {m n : ℕ}
    (hn : n+1≤p) {v w : Vec R s} (hv : v∈zeroSpace A m) (hw : w∈treeSpace A n) :
    v*w∈zeroSpace A (m+n) := by
  rw [← hadamard_apply]
  apply LinearMap.BilinMap.apply_apply_mem_of_mem_span _ _ _ hadamard _ _ _ hv hw
  rintro _ ⟨t,u,htu,ht,rfl⟩ _ ⟨r,hr,rfl⟩
  rw [hadamard_apply]
  have hu := treeDensity_isUnit_of_moments (hasMomentsThrough_of_treeOrder ho) r (by omega)
  rw [Tree.density,Nat.cast_mul] at hu
  obtain ⟨a,ha⟩ := isUnit_of_mul_isUnit_right hu
  have h := (zeroSpace A (m+n)).smul_mem (↑(a⁻¹):R)
    (mul_normDiff (A:=A) t u r htu ht hr)
  have hs : (↑(a⁻¹):R) • normTree A r = stageWeight A r := by
    rw [normTree,← ha,smul_smul,Units.inv_mul,one_smul]
  rw [← hs, mul_smul_comm]
  exact h

end Ring
end RKCert.Paired
