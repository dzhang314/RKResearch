module

public import RKResearch.OrderConditions
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Algebra.Field.Basic

@[expose] public section

/-!
# Mixed moments and native Runge–Kutta two-donor decoders

For each normalized rooted-tree column, weighted clock moments are
obtained from the actual reviewed order equations by adjoining leaves.
The two extra observations are individual physical rows with local
purity, not aggregate quadrature sites. An exact left inverse of this
small observation system decodes one monomial for each tree.
-/

namespace RKResearch.Certified.TwoDonorDense

open FiniteRootedTree
open scoped Matrix FiniteRootedTree BigOperators

section Base
variable {ι R : Type*} [Fintype ι] [CommSemiring R]

/-- Rooted-tree elementary column normalized by the forest factorial. -/
def normalized (A : Matrix ι ι R) (t : FiniteRootedTree) : ι → R :=
  (t.forestFactorial : R) • Φ t A

/-- The physical times of all stages. -/
def clocks (A : Matrix ι ι R) : ι → R := A *ᵥ 1

/-- Each tree through the stated size has its exact normalized monomial at this row. -/
def PureAt (A : Matrix ι ι R) (i : ι) (q : ℕ) : Prop :=
  ∀ t : FiniteRootedTree, (t.order : ℕ) ≤ q →
    normalized A t i = clocks A i ^ ((t.order : ℕ)-1)

theorem normalized_leaf (A : Matrix ι ι R) : normalized A leaf = 1 := by
  simp [normalized, forestFactorial]

/-- Root attachments of normalized columns include the right tree's size. -/
theorem normalized_join (A : Matrix ι ι R) (t u : FiniteRootedTree) :
    normalized A (t ◂ u) = normalized A t * ((u.order : R) • (A *ᵥ normalized A u)) := by
  simp only [normalized, Φ, forestFactorial, PNat.mul_coe, Nat.cast_mul,
    Matrix.mulVec_smul, smul_smul]
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.mul_apply]
  ac_rfl

/-- Cleared paid moments, without division, characteristic or positivity. -/
theorem cleared_moment {A : Matrix ι ι R} {b : ι → R} {p : ℕ}
    (h : HasOrder p A b) (t : FiniteRootedTree) (j : ℕ)
    (hpaid : (t.order : ℕ)+j ≤ p) :
    ((((t.order : ℕ)+j : ℕ) : R)) * (b ⬝ᵥ (normalized A t * (clocks A)^j)) = 1 := by
  have ht : ((t.addBush j).order : ℕ) ≤ p := by
    simpa only [order_addBush, PNat.add_coe] using hpaid
  have heq : normalized A t * (clocks A)^j =
      (t.forestFactorial : R) • Φ (t.addBush j) A := by
    funext i
    simp only [normalized, clocks, Φ_addBush, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    ac_rfl
  rw [heq, dotProduct_smul]
  simpa only [factorial_addBush, PNat.mul_coe, PNat.add_coe,
    Nat.cast_mul, smul_eq_mul, mul_assoc] using h (t.addBush j) ht

end Base

section Field
variable {ι K : Type*} [Fintype ι] [Field K] [CharZero K]

theorem moment {A : Matrix ι ι K} {b : ι → K} {p : ℕ} (h : HasOrder p A b)
    (t : FiniteRootedTree) (j : ℕ) (hpaid : (t.order : ℕ)+j ≤ p) :
    b ⬝ᵥ (normalized A t * (clocks A)^j) = 1 / ((((t.order : ℕ)+j : ℕ) : K)) := by
  have ht := t.order.pos
  have hne : ((((t.order : ℕ)+j : ℕ) : K)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  exact (eq_div_iff hne).mpr (by simpa only [mul_comm] using cleared_moment h t j hpaid)

variable (K) in
/-- On degree at most `q`: moments of powers `0,...,q-2`, then two evaluations. -/
def mixed (q : ℕ) (a b : K) : Matrix (Fin (q+1)) (Fin (q+1)) K :=
  fun i j =>
    if i.val < q-1 then 1 / (((i.val+j.val+1 : ℕ)) : K)
    else if i.val = q-1 then a^j.val else b^j.val

/-- The actual observations of an arbitrary stage-sized column. -/
def observations [DecidableEq ι] (q : ℕ) (A : Matrix ι ι K) (b : ι → K)
    (a₀ a₁ : ι) : Matrix (Fin (q+1)) ι K :=
  fun i =>
    if i.val < q-1 then b * (clocks A)^i.val
    else if i.val = q-1 then Pi.single a₀ 1 else Pi.single a₁ 1

/-- The exact observation column for the actual normalized tree column. -/
theorem observed_eq_column [DecidableEq ι] {q : ℕ}
    {A : Matrix ι ι K} {b : ι → K} {a₀ a₁ : ι} (h : HasOrder (2*q-1) A b)
    (h₀ : PureAt A a₀ (q+1)) (h₁ : PureAt A a₁ (q+1))
    (t : FiniteRootedTree) (ht : (t.order : ℕ) ≤ q+1) :
    observations q A b a₀ a₁ *ᵥ normalized A t =
      (mixed K q (clocks A a₀) (clocks A a₁)).col
        ⟨(t.order : ℕ)-1, by have := t.order.pos; omega⟩ := by
  funext i
  simp only [Matrix.mulVec, observations, Matrix.col_apply, mixed]
  split_ifs with hi h'
  · have he : i.val+((t.order : ℕ)-1)+1 = (t.order : ℕ)+i.val := by
      have := t.order.pos; omega
    rw [he, ← moment h t i.val (by omega)]
    unfold dotProduct
    apply Finset.sum_congr rfl
    intro j _
    simp only [Pi.mul_apply]
    rw [mul_assoc, mul_comm (((clocks A)^i.val) j)]
  · simpa only [single_dotProduct, one_mul] using h₀ t ht
  · simpa only [single_dotProduct, one_mul] using h₁ t ht

/-- A literal matrix decoder outputs the monomial's coefficient vector. -/
def IsDecoder (A : Matrix ι ι K) (q : ℕ) (D : Matrix (Fin (q+1)) ι K) : Prop :=
  ∀ (t : FiniteRootedTree) (ht : (t.order : ℕ) ≤ q+1),
    D *ᵥ normalized A t = Pi.single ⟨(t.order : ℕ)-1, by have := t.order.pos; omega⟩ 1

/-- An exact left inverse of the scalar mixed system yields a decoder
on every reviewed rooted tree on the paid size range. -/
theorem twoDonorDecoder [DecidableEq ι] {q : ℕ}
    {A : Matrix ι ι K} {b : ι → K} {a₀ a₁ : ι} (h : HasOrder (2*q-1) A b)
    (h₀ : PureAt A a₀ (q+1)) (h₁ : PureAt A a₁ (q+1))
    (L : Matrix (Fin (q+1)) (Fin (q+1)) K)
    (hinv : L * mixed K q (clocks A a₀) (clocks A a₁) = 1) :
    IsDecoder A q (L * observations q A b a₀ a₁) := by
  intro t ht
  rw [← Matrix.mulVec_mulVec, observed_eq_column h h₀ h₁ t ht,
    ← Matrix.mulVec_single_one, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]

end Field

#print axioms cleared_moment
#print axioms twoDonorDecoder
end RKResearch.Certified.TwoDonorDense
