module

public import RKCert.ReviewedNative.CanonicalSplitUniqueness
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Matrix.Rank

@[expose] public section

/-! Literal rooted series in an abstract commutative algebra. A linear
basis is enough to bound context rank, but is not a split stage algebra. -/
namespace RKResearch.ContextCompletion

open RKResearch FiniteRootedTree Module
open RKResearch.CanonicalUniqueness (TreeWord)
open scoped FiniteRootedTree BigOperators

/-- An abstract model need not carry coordinatewise stage multiplication. -/
structure Model (K V : Type*) [Field K] [CommRing V] [Algebra K V] where
  act : V →ₗ[K] V
  readout : V →ₗ[K] K

namespace Model

variable {K V : Type*} [Field K] [CommRing V] [Algebra K V]

@[simp] def column (M : Model K V) : FiniteRootedTree → V
  | .leaf => 1
  | .butcherProduct t u => M.column t * M.act (M.column u)

theorem column_unary (M : Model K V) (t : FiniteRootedTree) :
    M.column (.leaf ◂ t) = M.act (M.column t) := by
  simp only [column, one_mul]

theorem column_rootedSum (M : Model K V) (t u : FiniteRootedTree) :
    M.column (t # u) = M.column t * M.column u := by
  induction u with
  | leaf => simp only [rootedSum, column, mul_one]
  | butcherProduct base branch ih _ =>
    simp only [rootedSum, column, ih, mul_assoc]

/-- The input end of the reviewed one-hole word acts first. -/
def context (M : Model K V) : TreeWord → V →ₗ[K] V
  | .empty => LinearMap.id
  | .through C => (M.context C).comp M.act
  | .multiply u C => (M.context C).comp (LinearMap.mulLeft K (M.column u))

theorem context_insert (M : Model K V) (C : TreeWord) (t : FiniteRootedTree) :
    M.context C (M.column t) = M.column (C.insert t) := by
  induction C generalizing t with
  | empty => rfl
  | through C ih =>
    change M.context C (M.act (M.column t)) = M.column (C.insert (.leaf ◂ t))
    rw [← M.column_unary t]
    exact ih _
  | multiply u C ih =>
    change M.context C (M.column u * M.column t) = M.column (C.insert (u # t))
    rw [← M.column_rootedSum u t]
    exact ih _

def output (M : Model K V) (t : FiniteRootedTree) : K :=
  M.readout (M.column t)

/-- Arbitrary row and column indices, even when only selected cells are paid. -/
def block (M : Model K V) {ι κ : Type*} (contexts : ι → TreeWord)
    (trees : κ → FiniteRootedTree) : Matrix ι κ K :=
  fun i j => M.output ((contexts i).insert (trees j))

/-- The same denominator-cleared prescription as the reviewed tableau order,
without assuming the algebra splits as a coordinate algebra. -/
def HasOrder (M : Model K V) (p : ℕ) : Prop :=
  ∀ t : FiniteRootedTree, (t.order : ℕ) ≤ p → (t.factorial : K) * M.output t = 1

theorem HasOrder.paid_cell {M : Model K V} {p : ℕ} (h : M.HasOrder p)
    (C : TreeWord) (t : FiniteRootedTree) (paid : ((C.insert t).order : ℕ) ≤ p) :
    M.output (C.insert t) = ((C.insert t).factorial : K)⁻¹ := by
  have eq := h (C.insert t) paid
  have nz := (IsUnit.of_mul_eq_one _ eq).ne_zero
  calc
    M.output (C.insert t) =
        ((C.insert t).factorial : K)⁻¹ *
          (((C.insert t).factorial : K) * M.output (C.insert t)) := by
      rw [← mul_assoc, inv_mul_cancel₀ nz, one_mul]
    _ = ((C.insert t).factorial : K)⁻¹ := by rw [eq, mul_one]

theorem block_rank_le (M : Model K V) [Module.Finite K V]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (contexts : ι → TreeWord) (trees : κ → FiniteRootedTree) :
    (M.block contexts trees).rank ≤ Module.finrank K V := by
  classical
  let β := Module.finBasis K V
  let U : Matrix ι (Fin (Module.finrank K V)) K :=
    fun i k => M.readout (M.context (contexts i) (β k))
  let W : Matrix (Fin (Module.finrank K V)) κ K :=
    fun k j => β.repr (M.column (trees j)) k
  have factor : M.block contexts trees = U * W := by
    ext i j
    change M.readout (M.column ((contexts i).insert (trees j))) = (U * W) i j
    rw [← M.context_insert (contexts i) (trees j), Matrix.mul_apply]
    let r := M.readout.comp (M.context (contexts i))
    have val := congrArg (fun v => r v) (β.sum_repr (M.column (trees j)))
    simp only [map_sum, map_smul, smul_eq_mul] at val
    change r (M.column (trees j)) = ∑ k, r (β k) * β.repr (M.column (trees j)) k
    rw [← val]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [factor]
  exact (Matrix.rank_mul_le_left U W).trans
    ((Matrix.rank_le_card_width U).trans_eq (Fintype.card_fin _))

end Model
end RKResearch.ContextCompletion
