module

public import RKCert.ReviewedNative.TwoDonorDense

@[expose] public section

/-!
# Native symbolic order boost with paid old and new moment rows

Induct on the reviewed binary constructor, proving all decorated
moments of that rooted tree at once. A small attached branch merely
shifts the base moment index. An oversized attached branch can only
have a small base, and its new moments are already available by
induction. No global largest-child enumeration is needed.
-/

namespace RKResearch.Certified.TwoOrderMomentTail

open FiniteRootedTree TwoDonorDense
open scoped Matrix FiniteRootedTree BigOperators

variable {ι η K : Type*} [Fintype ι] [Fintype η] [Field K] [CharZero K]

/-- Extend an unchanged old prefix by a new weighted tail. -/
def tableau (A : Matrix ι ι K) (U : Matrix η ι K) (B : Matrix η η K) :
    Matrix (ι ⊕ η) (ι ⊕ η) K := Matrix.fromBlocks A 0 U B

def head (x : ι ⊕ η → K) : ι → K := x ∘ Sum.inl
def tail (x : ι ⊕ η → K) : η → K := x ∘ Sum.inr

theorem head_action (A : Matrix ι ι K) (U : Matrix η ι K) (B : Matrix η η K)
    (x : ι ⊕ η → K) :
    head (tableau A U B *ᵥ x) = A *ᵥ head x := by
  funext i
  simp [head, tableau, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]

theorem tail_action (A : Matrix ι ι K) (U : Matrix η ι K) (B : Matrix η η K)
    (x : ι ⊕ η → K) :
    tail (tableau A U B *ᵥ x) = U *ᵥ head x + B *ᵥ tail x := by
  funext i
  simp [head, tail, tableau, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]

theorem head_normalized (A : Matrix ι ι K) (U : Matrix η ι K) (B : Matrix η η K)
    (t : FiniteRootedTree) :
    head (normalized (tableau A U B) t) = normalized A t := by
  induction t with
  | leaf => simp [normalized_leaf]; rfl
  | butcherProduct t u ht hu =>
    rw [normalized_join, normalized_join]
    change head (normalized (tableau A U B) t) *
      ((u.order : K) • head (tableau A U B *ᵥ normalized (tableau A U B) u)) = _
    rw [head_action, ht, hu]

def row {α : Type*} (b c : α → K) (j : ℕ) : α → K := b * c^j

def read {α : Type*} [Fintype α] (b c : α → K) (j : ℕ) (x : α → K) : K :=
  row b c j ⬝ᵥ x

theorem read_eq_moment {α : Type*} [Fintype α] (b c x : α → K) (j : ℕ) :
    read b c j x = b ⬝ᵥ (x*c^j) := by
  unfold read row dotProduct
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.mul_apply]
  ac_rfl

theorem read_times_power {α : Type*} [Fintype α] (b c x : α → K) (j k : ℕ) :
    read b c j (x*c^k) = read b c (j+k) x := by
  unfold read row dotProduct
  apply Finset.sum_congr rfl
  intro i _
  simp only [pow_add, Pi.mul_apply]
  ac_rfl

theorem normalized_output_eq_order {α : Type*} [Fintype α] (A : Matrix α α K) (b : α → K)
    (p : ℕ) (h : ∀ t : FiniteRootedTree, (t.order : ℕ) ≤ p →
      b ⬝ᵥ normalized A t = 1 / (t.order : K)) : HasOrder p A b := by
  intro t ht
  have hne : (t.order : K) ≠ 0 := Nat.cast_ne_zero.mpr (by have := t.order.pos; omega)
  have hw := h t ht
  rw [normalized, dotProduct_smul, smul_eq_mul] at hw
  rw [factorial, PNat.mul_coe, Nat.cast_mul, mul_assoc, hw, mul_comm, div_mul_cancel₀ _ hne]

/-- All new stage columns are pure through size `q+1` if the proposed
block feed gives the exact integrated monomial on every old low column. -/
theorem low_pure {q : ℕ} {A : Matrix ι ι K} {U : Matrix η ι K} {B : Matrix η η K}
    {c : η → K}
    (hfeed : ∀ t : FiniteRootedTree, (t.order : ℕ) ≤ q →
      U *ᵥ normalized A t + B *ᵥ (c^((t.order : ℕ)-1)) =
      ((1 / (t.order : K)) : K) • c^(t.order : ℕ)) :
    ∀ t : FiniteRootedTree, (t.order : ℕ) ≤ q+1 →
      tail (normalized (tableau A U B) t) = c^((t.order : ℕ)-1) := by
  intro t
  induction t with
  | leaf => intro _; simp [normalized_leaf, order]; rfl
  | butcherProduct t u ihT ihU =>
    intro ht
    have hT := t.order.pos
    have hU := u.order.pos
    have hs : ((t ◂ u).order : ℕ) = (t.order : ℕ)+(u.order : ℕ) := rfl
    have he : ((t ◂ u).order : ℕ)-1 = (t.order : ℕ)-1+(u.order : ℕ) := by omega
    have hne : (u.order : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [normalized_join]
    change tail (normalized (tableau A U B) t) *
      ((u.order : K) • tail (tableau A U B *ᵥ normalized (tableau A U B) u)) = _
    rw [ihT (by omega), tail_action, head_normalized, ihU (by omega), hfeed u (by omega),
      smul_smul, mul_comm (u.order : K), div_mul_cancel₀ _ hne, one_smul, he, pow_add]

/-- A finite way to state the reverse weighted row arrays and their exact
scalar moment budget. Entries of `G` above `j+1` and `H` above
`j-1` are identically zero. -/
structure Adjoints (q : ℕ) (A : Matrix ι ι K) (b : ι → K)
    (U : Matrix η ι K) (B : Matrix η η K) (w c : η → K) where
  G : Matrix (Fin q) (Fin (q+1)) K
  H : Matrix (Fin q) (Fin (q+1)) K
  gbound : ∀ j k, j.val+1 < k.val → G j k = 0
  hbound : ∀ j k, j.val ≤ k.val → H j k = 0
  rows : ∀ (j : Fin q) (y : ι → K) (z : η → K),
    read w c j.val (U *ᵥ y + B *ᵥ z) =
      (∑ k : Fin (q+1), G j k * read w c k.val z) +
      (∑ k : Fin (q+1), H j k * read b (clocks A) k.val y)
  scalar : ∀ (j : Fin q) (m : ℕ), q < m → m+j.val+1 ≤ 2*q+1 →
    (m : K) * (∑ k : Fin (q+1), G j k * (1 / ((m+k.val : ℕ) : K)) +
      ∑ k : Fin (q+1), H j k * (1 / ((m+k.val : ℕ) : K))) =
      1 / ((m+j.val+1 : ℕ) : K)

theorem tail_moments {q : ℕ} {A : Matrix ι ι K} {b : ι → K}
    {U : Matrix η ι K} {B : Matrix η η K} {w c : η → K}
    (hold : HasOrder (2*q-1) A b)
    (hquad : ∀ j : ℕ, j < 2*q+1 → read w c j 1 = 1 / ((j+1 : ℕ) : K))
    (hfeed : ∀ t : FiniteRootedTree, (t.order : ℕ) ≤ q →
      U *ᵥ normalized A t + B *ᵥ (c^((t.order : ℕ)-1)) =
      ((1 / (t.order : K)) : K) • c^(t.order : ℕ))
    (F : Adjoints q A b U B w c) :
    ∀ (t : FiniteRootedTree) (j : ℕ), (t.order : ℕ)+j ≤ 2*q+1 →
      read w c j (tail (normalized (tableau A U B) t)) =
        1 / ((((t.order : ℕ)+j : ℕ) : K)) := by
  intro t
  induction t with
  | leaf =>
    intro j hj
    have hs : (leaf.order : ℕ) = 1 := rfl
    have h1 : tail (normalized (tableau A U B) leaf) = 1 := by rw [normalized_leaf]; rfl
    rw [h1, hs, hquad j (by omega), Nat.add_comm j]
  | butcherProduct t u ihT ihU =>
    intro j h
    have hT := t.order.pos
    have hU := u.order.pos
    have hs : ((t ◂ u).order : ℕ) = (t.order : ℕ)+(u.order : ℕ) := rfl
    have hne : (u.order : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [normalized_join]
    change read w c j (tail (normalized (tableau A U B) t) *
      ((u.order : K) • tail (tableau A U B *ᵥ normalized (tableau A U B) u))) = _
    rw [tail_action, head_normalized]
    by_cases hu : (u.order : ℕ) ≤ q
    · rw [low_pure hfeed u (by omega), hfeed u hu, smul_smul, mul_comm (u.order : K),
        div_mul_cancel₀ _ hne, one_smul, read_times_power, ihT _ (by omega)]
      congr 2
      omega
    · have ht : (t.order : ℕ) ≤ q+1 := by omega
      let r : Fin q := ⟨j+((t.order : ℕ)-1), by omega⟩
      have hsplit : (u.order : ℕ)+r.val+1 = ((t ◂ u).order : ℕ)+j := by
        dsimp [r]; omega
      rw [low_pure hfeed t ht]
      have hstep : ∀ x : η → K, read w c j (c^((t.order : ℕ)-1) * ((u.order : K) • x)) =
          (u.order : K) * read w c r.val x := by
        intro x
        rw [mul_comm (c^_)]
        change read w c j (((u.order : K) • x)*c^((t.order : ℕ)-1)) = _
        rw [read_times_power]
        simp only [r, read, dotProduct_smul, smul_eq_mul]
      rw [hstep, F.rows]
      have hg : (∑ k : Fin (q+1), F.G r k * read w c k.val
            (tail (normalized (tableau A U B) u))) =
          ∑ k : Fin (q+1), F.G r k * (1 / (((u.order : ℕ)+k.val : ℕ) : K)) := by
        apply Finset.sum_congr rfl
        intro k _
        by_cases hk : r.val+1 < k.val
        · rw [F.gbound r k hk, zero_mul, zero_mul]
        · rw [ihU k.val (by omega)]
      have hh : (∑ k : Fin (q+1), F.H r k * read b (clocks A) k.val (normalized A u)) =
          ∑ k : Fin (q+1), F.H r k * (1 / (((u.order : ℕ)+k.val : ℕ) : K)) := by
        apply Finset.sum_congr rfl
        intro k _
        by_cases hk : r.val ≤ k.val
        · rw [F.hbound r k hk, zero_mul, zero_mul]
        · rw [read_eq_moment, moment hold u k.val (by omega)]
      rw [hg, hh]
      have hscalar := F.scalar r (u.order : ℕ) (by omega) (by omega)
      rw [hsplit] at hscalar
      exact hscalar

/-- The ordinary rooted-tree order result on the actual fixed old/new blocks. -/
theorem tail_hasOrder {q : ℕ} {A : Matrix ι ι K} {b : ι → K}
    {U : Matrix η ι K} {B : Matrix η η K} {w c : η → K}
    (hold : HasOrder (2*q-1) A b)
    (hquad : ∀ j : ℕ, j < 2*q+1 → read w c j 1 = 1 / ((j+1 : ℕ) : K))
    (hfeed : ∀ t : FiniteRootedTree, (t.order : ℕ) ≤ q →
      U *ᵥ normalized A t + B *ᵥ (c^((t.order : ℕ)-1)) =
      ((1 / (t.order : K)) : K) • c^(t.order : ℕ))
    (F : Adjoints q A b U B w c) :
    HasOrder (2*q+1) (tableau A U B) (Sum.elim 0 w) := by
  apply normalized_output_eq_order
  intro t ht
  have hw := tail_moments hold hquad hfeed F t 0 (by omega)
  simp only [read, row, pow_zero, mul_one, Nat.add_zero] at hw
  simpa [dotProduct, Fintype.sum_sum_type, tail] using hw

#print axioms tail_hasOrder
end RKResearch.Certified.TwoOrderMomentTail
