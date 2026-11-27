module

public import RKResearch.OrderConditions
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-! # A certificate for forests with equal normalized stage vectors

The reviewed binary tree constructor has a bilinear normalized stage
action. Hence one can merge two equal vectors at the same grade without
requiring the underlying rooted trees to coincide. A finite table of
closed joins covers every reviewed tree by structural induction. -/

namespace RKResearch.Certified.ERKNormalizedVectorCover
open RKResearch FiniteRootedTree
open scoped Matrix FiniteRootedTree

variable {ι R : Type*} [Fintype ι] [CommSemiring R]

def normStage (A : Matrix ι ι R) (t : FiniteRootedTree) : ι → R :=
  ((t.forestFactorial:ℕ):R) • Φ t A

theorem norm_leaf (A : Matrix ι ι R) : normStage A leaf = 1 := by
  simp [normStage]

theorem norm_product (A : Matrix ι ι R) (t u : FiniteRootedTree) :
    normStage A (t ◂ u) =
      normStage A t * (((u.order:ℕ):R) • (A *ᵥ normStage A u)) := by
  rw [normStage,normStage,normStage,Φ,forestFactorial,Matrix.mulVec_smul]
  simp only [PNat.mul_coe,Nat.cast_mul]
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.mul_apply]
  ac_rfl

theorem cover {Z : Type*} {p : ℕ} {A : Matrix ι ι R}
    {g : Z → ℕ} {V W : Z → ι → R}
    {root : Z} {join : Z → Z → Z}
    (hroot : g root = 1 ∧ V root = 1)
    (hjoin : ∀ i j, g i + g j ≤ p →
      g (join i j) = g i + g j ∧ V (join i j) = V i * W j)
    (hact : ∀ j, g j < p → W j = (g j:R) • (A *ᵥ V j))
    (t : FiniteRootedTree) (ht : (t.order:ℕ) ≤ p) :
    ∃ i, g i = (t.order:ℕ) ∧ V i = normStage A t := by
  induction t with
  | leaf => exact ⟨root, hroot.1, hroot.2.trans (norm_leaf _).symm⟩
  | butcherProduct u v ihu ihv =>
    have hsum : (u.order:ℕ) + (v.order:ℕ) ≤ p := ht
    have hpu := u.order.pos
    obtain ⟨i,hi,hu⟩ := ihu (by omega)
    obtain ⟨j,hj,hv⟩ := ihv (by omega)
    have hc := hjoin i j (by rwa [hi,hj])
    have ha := hact j (by rw [hj]; omega)
    exact ⟨join i j, by simpa only [hi,hj,order,PNat.add_coe] using hc.1,
      by rw [hc.2,ha,hj,hu,hv,norm_product]⟩

theorem factorial_moment (A : Matrix ι ι R) (b : ι → R) (t : FiniteRootedTree) :
    (t.factorial:R) * (b ⬝ᵥ Φ t A) =
      ((t.order:ℕ):R) * (b ⬝ᵥ normStage A t) := by
  simp only [normStage,dotProduct_smul,smul_eq_mul,factorial,PNat.mul_coe,Nat.cast_mul]
  ac_rfl

end RKResearch.Certified.ERKNormalizedVectorCover
