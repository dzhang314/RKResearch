module

public import Mathlib.Data.Matrix.Mul
public import RKResearch.FiniteRootedTree

public section

namespace RKResearch

open FiniteRootedTree
open scoped Matrix

variable {ι R : Type _} [Fintype ι] [CommSemiring R]

@[expose, simp] def Φ : FiniteRootedTree → Matrix ι ι R → ι → R
  | leaf, _ => 1
  | base ◂ branch, A => Φ base A * (A *ᵥ Φ branch A)

theorem Φ_branch_swap (t u v : FiniteRootedTree) (A : Matrix ι ι R) :
    Φ ((t ◂ u) ◂ v) A = Φ ((t ◂ v) ◂ u) A := by apply mul_right_comm

theorem Φ_rootedSum (t u : FiniteRootedTree) (A : Matrix ι ι R) :
    Φ (t # u) A = Φ t A * Φ u A := by
  induction u with
  | leaf => simp
  | butcherProduct base branch ih _ => simp only [rootedSum, Φ, ih, mul_assoc]

theorem Φ_addBush (t : FiniteRootedTree) (k : ℕ) (A : Matrix ι ι R) :
    Φ (t.addBush k) A = Φ t A * (A *ᵥ 1) ^ k := by
  induction k with
  | zero => simp only [addBush, pow_zero, mul_one]
  | succ k ih => simp only [addBush, Φ, ih, pow_succ, mul_assoc]

theorem Φ_bushyTree (n : ℕ+) (A : Matrix ι ι R) :
    Φ (bushyTree n) A = (A *ᵥ 1) ^ ((n : ℕ) - 1) := by
  simp only [bushyTree, PNat.natPred, Φ_addBush, Φ, one_mul]

theorem Φ_tallTree [DecidableEq ι] (n : ℕ+) (A : Matrix ι ι R) :
    Φ (tallTree n) A = A ^ ((n : ℕ) - 1) *ᵥ 1 := by
  unfold tallTree
  induction n <;> (dsimp; simp [*, mul_pow_sub_one])

@[expose] def HasOrder (p : ℕ) (A : Matrix ι ι R) (b : ι → R) : Prop :=
  ∀ t : FiniteRootedTree, t.order ≤ p → (t.factorial : R) * (b ⬝ᵥ Φ t A) = 1

@[expose] def HasQuadratureOrder (p : ℕ) (b c : ι → R) : Prop :=
  ∀ k < p, k.succ * (b ⬝ᵥ c ^ k) = 1

theorem HasOrder.hasQuadratureOrder {p : ℕ} {A : Matrix ι ι R} {b : ι → R}
    (h : HasOrder p A b) : HasQuadratureOrder p b (A *ᵥ 1) := by
  intro k
  specialize h (bushyTree k.succPNat)
  simp only [order_bushyTree, factorial_bushyTree, Φ_bushyTree] at h
  assumption

theorem HasQuadratureOrder.isUnit {p n : ℕ} {b c : ι → R}
    (h : HasQuadratureOrder p b c) (hn : 0 < n) (hp : n ≤ p) :
    IsUnit (n : R) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  apply IsUnit.of_mul_eq_one _ (h k hp)

section Homomorphisms

variable {S : Type _} [CommSemiring S]

theorem map_Φ (f : R →+* S) (t : FiniteRootedTree) (A : Matrix ι ι R) :
    f ∘ Φ t A = Φ t (A.map f) := by
  have map_mulVec (v : ι → R) : f ∘ (A *ᵥ v) = A.map f *ᵥ (f ∘ v) :=
    funext (f.map_mulVec A v)
  induction t <;> simp only [Φ, map_comp_one, map_comp_mul, *]

variable {p : ℕ} {A : Matrix ι ι R} {b : ι → R}

theorem HasOrder.map (h : HasOrder p A b) (f : R →+* S) :
    HasOrder p (A.map f) (f ∘ b) := by
  intro t ht
  simpa only [RingHom.map_mul, map_natCast, RingHom.map_dotProduct,
    map_Φ, RingHom.map_one] using congrArg f (h t ht)

theorem hasOrder_map_iff {f : R →+* S} (hf : Function.Injective f) :
    HasOrder p (A.map f) (f ∘ b) ↔ HasOrder p A b := by
  constructor
  · intro h t ht
    apply hf
    simpa only [RingHom.map_mul, map_natCast, RingHom.map_dotProduct,
      map_Φ, RingHom.map_one] using h t ht
  · exact (·.map f)

end Homomorphisms

end RKResearch
