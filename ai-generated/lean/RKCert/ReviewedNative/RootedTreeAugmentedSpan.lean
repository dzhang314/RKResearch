module

public import RKCert.ReviewedNative.FiniteScaledOrderCheck
public import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.Ring

@[expose] public section

/-! A fixed tableau's exact scaled order conditions are a graded bilinear
closure into linear kernels. This does not enumerate rooted trees. -/
namespace RKResearch.Certified.RootedTreeAugmentedSpan

open RKResearch RKResearch.FiniteRootedTree
open scoped Matrix FiniteRootedTree

abbrev Feature (ι R : Type*) := (ι → R) × R

def degree (t : FiniteRootedTree) : ℕ := t.order

@[simp] theorem degree_leaf : degree leaf = 1 := rfl

@[simp] theorem degree_attach (t u : FiniteRootedTree) :
    degree (t ◂ u) = degree t + degree u := by
  simp only [degree, order, PNat.add_coe]

theorem degree_pos (t : FiniteRootedTree) : 0 < degree t := t.order.pos

section Stage

variable {ι R : Type*} [Fintype ι] [CommSemiring R]

/-- Numerator vector times the reviewed forest factorial, not the whole
tree factorial. Its ordinary stage factor retains degree `order - 1`. -/
def forestVector (A : Matrix ι ι R) (t : FiniteRootedTree) : ι → R :=
  ((t.forestFactorial : ℕ) : R) • Φ t A

@[simp] theorem forestVector_leaf (A : Matrix ι ι R) :
    forestVector A leaf = 1 := by
  simp [forestVector, forestFactorial, Φ]

theorem forestVector_attach (A : Matrix ι ι R) (t u : FiniteRootedTree) :
    forestVector A (t ◂ u) =
      forestVector A t * (A *ᵥ ((degree u : R) • forestVector A u)) := by
  simp only [forestVector, forestFactorial, degree, PNat.mul_coe, Nat.cast_mul,
    Φ, smul_smul, Matrix.mulVec_smul]
  funext i
  simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  ac_rfl

theorem order_mul_out_forestVector (A : Matrix ι ι R) (b : ι → R)
    (t : FiniteRootedTree) :
    (degree t : R) * (b ⬝ᵥ forestVector A t) =
      (t.factorial : R) * (b ⬝ᵥ Φ t A) := by
  change ((t.order : ℕ) : R) * (b ⬝ᵥ forestVector A t) =
    ((t.factorial : ℕ) : R) * (b ⬝ᵥ Φ t A)
  simp only [forestVector, dotProduct_smul, smul_eq_mul, factorial,
    PNat.mul_coe, Nat.cast_mul, mul_assoc]

/-- The last coordinate retains exactly the checked stage-scale power.
No invertibility or cancellation is used to construct this feature. -/
def feature (A : Matrix ι ι R) (d : R) (t : FiniteRootedTree) : Feature ι R :=
  (forestVector A t, d ^ (degree t - 1))

@[simp] theorem feature_leaf (A : Matrix ι ι R) (d : R) :
    feature A d leaf = ((1 : ι → R), (1 : R)) := by
  simp [feature]

def attachValue (A : Matrix ι ι R) (d : R) (q : ℕ) (x y : Feature ι R) :
    Feature ι R :=
  (x.1 * (A *ᵥ ((q : R) • y.1)), (d * x.2) * y.2)

theorem feature_attach (A : Matrix ι ι R) (d : R) (t u : FiniteRootedTree) :
    feature A d (t ◂ u) = attachValue A d (degree u) (feature A d t) (feature A d u) := by
  apply Prod.ext
  · exact forestVector_attach A t u
  · have ht := degree_pos t
    have hu := degree_pos u
    have addpow :
        degree (t ◂ u) - 1 = (1 + (degree t - 1)) + (degree u - 1) := by
      rw [degree_attach]
      omega
    change d ^ (degree (t ◂ u) - 1) =
      (d * d ^ (degree t - 1)) * d ^ (degree u - 1)
    rw [addpow]
    simp only [pow_add, pow_one]

end Stage

section Bilinear

variable {ι R : Type*} [Fintype ι] [CommRing R]

private theorem attachValue_add_left (A : Matrix ι ι R) (d : R) (q : ℕ)
    (x y z : Feature ι R) :
    attachValue A d q (x+y) z = attachValue A d q x z + attachValue A d q y z := by
  apply Prod.ext
  · funext i
    change (x.1 i + y.1 i) * (A *ᵥ ((q : R) • z.1)) i =
      x.1 i * (A *ᵥ ((q : R) • z.1)) i + y.1 i * (A *ᵥ ((q : R) • z.1)) i
    exact add_mul _ _ _
  · change (d * (x.2 + y.2)) * z.2 = (d*x.2)*z.2 + (d*y.2)*z.2
    ring

theorem attachValue_add_right (A : Matrix ι ι R) (d : R) (q : ℕ)
    (x y z : Feature ι R) :
    attachValue A d q x (y+z) = attachValue A d q x y + attachValue A d q x z := by
  apply Prod.ext
  · change x.1 * (A *ᵥ ((q : R) • (y.1 + z.1))) =
      x.1 * (A *ᵥ ((q : R) • y.1)) + x.1 * (A *ᵥ ((q : R) • z.1))
    rw [smul_add, Matrix.mulVec_add]
    funext i
    exact mul_add (x.1 i) ((A *ᵥ ((q : R) • y.1)) i) ((A *ᵥ ((q : R) • z.1)) i)
  · change (d*x.2)*(y.2+z.2) = (d*x.2)*y.2+(d*x.2)*z.2
    exact mul_add _ _ _

private theorem attachValue_smul_left (A : Matrix ι ι R) (d : R) (q : ℕ)
    (c : R) (x y : Feature ι R) :
    attachValue A d q (c • x) y = c • attachValue A d q x y := by
  apply Prod.ext
  · funext i
    change (c * x.1 i) * (A *ᵥ ((q : R) • y.1)) i =
      c * (x.1 i * (A *ᵥ ((q : R) • y.1)) i)
    exact mul_assoc _ _ _
  · change (d*(c*x.2))*y.2 = c*((d*x.2)*y.2)
    ring

theorem attachValue_smul_right (A : Matrix ι ι R) (d : R) (q : ℕ)
    (c : R) (x y : Feature ι R) :
    attachValue A d q x (c • y) = c • attachValue A d q x y := by
  apply Prod.ext
  · change x.1 * (A *ᵥ ((q : R) • (c • y.1))) =
      c • (x.1 * (A *ᵥ ((q : R) • y.1)))
    have hs : (q : R) • (c • y.1) = c • ((q : R) • y.1) := by
      simp only [smul_smul, mul_comm (q : R) c]
    rw [hs, Matrix.mulVec_smul]
    funext i
    change x.1 i * (c * (A *ᵥ ((q : R) • y.1)) i) =
      c * (x.1 i * (A *ᵥ ((q : R) • y.1)) i)
    exact mul_left_comm _ _ _
  · change (d*x.2)*(c*y.2) = c*((d*x.2)*y.2)
    ring

/-- At a fixed child degree the exact attachment is bilinear, including
the one extra stage-scale factor on its last coordinate. -/
def attachBilin (A : Matrix ι ι R) (d : R) (q : ℕ) :
    Feature ι R →ₗ[R] Feature ι R →ₗ[R] Feature ι R where
  toFun x :=
    { toFun := attachValue A d q x
      map_add' := attachValue_add_right A d q x
      map_smul' := fun c y => attachValue_smul_right A d q c x y }
  map_add' x y := by
    apply LinearMap.ext
    intro z
    exact attachValue_add_left A d q x y z
  map_smul' c x := by
    apply LinearMap.ext
    intro y
    exact attachValue_smul_left A d q c x y

@[simp] theorem attachBilin_apply (A : Matrix ι ι R) (d : R) (q : ℕ)
    (x y : Feature ι R) : attachBilin A d q x y = attachValue A d q x y := rfl

/-- The original paid equality, after grouping the exact forest factorial. -/
def residual (b : ι → R) (e : R) (n : ℕ) : Feature ι R →ₗ[R] R where
  toFun x := (n : R) * (b ⬝ᵥ x.1) - e*x.2
  map_add' x y := by
    change (n : R) * (b ⬝ᵥ (x.1+y.1)) - e*(x.2+y.2) =
      ((n : R)*(b ⬝ᵥ x.1)-e*x.2) + ((n : R)*(b ⬝ᵥ y.1)-e*y.2)
    rw [dotProduct_add]
    ring
  map_smul' c x := by
    change (n : R) * (b ⬝ᵥ (c • x.1)) - e*(c*x.2) =
      c * ((n : R)*(b ⬝ᵥ x.1)-e*x.2)
    rw [dotProduct_smul]
    simp only [smul_eq_mul]
    ring

/-- A generating family suffices; linear independence, exact dimensions,
and which features are generators are not soundness hypotheses. -/
def BasisCloses (A : Matrix ι ι R) (d : R) (p : ℕ)
    (B : ℕ → Set (Feature ι R)) : Prop :=
  ∀ k l : ℕ, 0 < k → 0 < l → k+l ≤ p →
    ∀ x ∈ B k, ∀ y ∈ B l, attachBilin A d l x y ∈ Submodule.span R (B (k+l))

theorem all_features_of_basis_closure (A : Matrix ι ι R) (d : R) (p : ℕ)
    (B : ℕ → Set (Feature ι R))
    (base : ((1 : ι → R), (1 : R)) ∈ Submodule.span R (B 1))
    (close : BasisCloses A d p B) :
    ∀ t : FiniteRootedTree, degree t ≤ p →
      feature A d t ∈ Submodule.span R (B (degree t)) := by
  intro t
  induction t with
  | leaf =>
    intro _
    simpa only [feature_leaf, degree_leaf] using base
  | butcherProduct t u it iu =>
    intro h
    have hsum : degree t + degree u ≤ p := by simpa only [degree_attach] using h
    have ht : degree t ≤ p := (Nat.le_add_right _ _).trans hsum
    have hu : degree u ≤ p := (Nat.le_add_left _ _).trans hsum
    have hs : attachBilin A d (degree u) (feature A d t) (feature A d u) ∈
        Submodule.span R (B (degree t + degree u)) :=
      LinearMap.BilinMap.apply_apply_mem_of_mem_span _ _ _ _
        (close (degree t) (degree u) (degree_pos t) (degree_pos u) hsum)
        _ _ (it ht) (iu hu)
    simpa only [degree_attach, feature_attach, attachBilin_apply] using hs

/-- Native order certificates by graded span closure, without tree enumeration. -/
theorem all_scaled_moments_of_basis_closure (A : Matrix ι ι R) (b : ι → R)
    (d e : R) (p : ℕ) (B : ℕ → Set (Feature ι R))
    (base : ((1 : ι → R), (1 : R)) ∈ Submodule.span R (B 1))
    (close : BasisCloses A d p B)
    (paid : ∀ n : ℕ, 0 < n → n ≤ p → ∀ x ∈ B n, residual b e n x = 0) :
    ∀ t : FiniteRootedTree, (t.order : ℕ) ≤ p →
      (t.factorial : R) * (b ⬝ᵥ Φ t A) = e * d^((t.order : ℕ)-1) := by
  intro t ht
  have hs := all_features_of_basis_closure A d p B base close t ht
  have hk : Submodule.span R (B (degree t)) ≤ (residual b e (degree t)).ker := by
    apply Submodule.span_le.mpr
    intro x hx
    exact LinearMap.mem_ker.mpr (paid (degree t) (degree_pos t) ht x hx)
  have hz : residual b e (degree t) (feature A d t) = 0 := LinearMap.mem_ker.mp (hk hs)
  change (degree t : R) * (b ⬝ᵥ forestVector A t) -
    e * d ^ (degree t - 1) = 0 at hz
  rw [order_mul_out_forestVector A b t] at hz
  exact sub_eq_zero.mp hz

variable {K : Type*} [CommSemiring K]

/-- Checked scaled spans feed the original reviewed result at the same tableau. -/
theorem hasOrder_of_basis_closure (A : Matrix ι ι R) (b : ι → R)
    (U : Matrix ι ι K) (w : ι → K) (f : R →+* K)
    (d e : R) (p : ℕ) (B : ℕ → Set (Feature ι R))
    (hA : A.map f = f d • U) (hb : f ∘ b = f e • w)
    (hd : IsUnit (f d)) (he : IsUnit (f e))
    (base : ((1 : ι → R), (1 : R)) ∈ Submodule.span R (B 1))
    (close : BasisCloses A d p B)
    (paid : ∀ n : ℕ, 0 < n → n ≤ p → ∀ x ∈ B n, residual b e n x = 0) :
    RKResearch.HasOrder p U w :=
  hasOrder_of_scaled_moments f hA hb hd he
    (all_scaled_moments_of_basis_closure A b d e p B base close paid)

end Bilinear

section Clear

variable {V K : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- A checker may use a nonzero clearing denominator for a coordinate
vector membership, but must verify it is invertible in this field. -/
theorem span_mem_of_cleared (W : Submodule K V) {c : K} (hc : c ≠ 0)
    {x : V} (h : c • x ∈ W) : x ∈ W := by
  simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using W.smul_mem c⁻¹ h

end Clear

end RKResearch.Certified.RootedTreeAugmentedSpan
