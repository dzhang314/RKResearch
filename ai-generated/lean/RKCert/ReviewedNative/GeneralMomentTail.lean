module

public import RKCert.ReviewedNative.TailMatrixReceipts

@[expose] public section

/-!
# Even/odd native moment tails with independently paid old frontiers

The tail output proof can take different kinds of old degree payments.
In a two-order lift, the last reverse clock can be arbitrary when the
sole highest frontier is paid by a genuine one-grade-larger decoder.
The preceding moment rows still use only the old ordinary order.
-/

namespace RKResearch.Certified.TwoOrderMomentTail

open FiniteRootedTree TwoDonorDense
open scoped Matrix FiniteRootedTree BigOperators

variable {ι η K : Type*} [Fintype ι] [Fintype η] [Field K] [CharZero K]

/-- Old-read constraints can be sourced from either ordinary old
quadrature or a separate verified polynomial decoder. -/
structure GeneralAdjoints (q r : ℕ) (A : Matrix ι ι K)
    (U : Matrix η ι K) (B : Matrix η η K) (w c : η → K) where
  G : Matrix (Fin r) (Fin (r+1)) K
  H : Matrix (Fin r) (Fin (r+1)) K
  oldRow : Matrix (Fin r) ι K
  gbound : ∀ j k, j.val+1 < k.val → G j k = 0
  rows : ∀ (j : Fin r) (y : ι → K) (z : η → K),
    read w c j.val (U *ᵥ y + B *ᵥ z) =
      (∑ k : Fin (r+1), G j k * read w c k.val z) + oldRow j ⬝ᵥ y
  old_pay : ∀ (j : Fin r) (t : FiniteRootedTree),
    q < (t.order : ℕ) → (t.order : ℕ)+j.val+1 ≤ q+r+1 →
    oldRow j ⬝ᵥ normalized A t =
      ∑ k : Fin (r+1), H j k * (1 / ((((t.order : ℕ)+k.val : ℕ)) : K))
  scalar : ∀ (j : Fin r) (m : ℕ), q < m → m+j.val+1 ≤ q+r+1 →
    (m : K) * (∑ k : Fin (r+1), G j k * (1 / ((m+k.val : ℕ) : K)) +
      ∑ k : Fin (r+1), H j k * (1 / ((m+k.val : ℕ) : K))) =
      1 / ((m+j.val+1 : ℕ) : K)

/-- Fit the actual row equations by finite matrix multiplication, with
old paid observations supplied directly. -/
theorem general_rows_from_matrices {r : ℕ}
    {U : Matrix η ι K} {B : Matrix η η K} {w c : η → K}
    (G : Matrix (Fin r) (Fin (r+1)) K) (oldRow : Matrix (Fin r) ι K)
    (hG : momentRows r w c * B = G * momentRows (r+1) w c)
    (hU : momentRows r w c * U = oldRow)
    (j : Fin r) (y : ι → K) (z : η → K) :
    read w c j.val (U *ᵥ y + B *ᵥ z) =
      (∑ k : Fin (r+1), G j k * read w c k.val z) + oldRow j ⬝ᵥ y := by
  have hh : (momentRows r w c *ᵥ (U *ᵥ y)) j = (oldRow *ᵥ y) j := by
    rw [Matrix.mulVec_mulVec, hU]
  have hg : (momentRows r w c *ᵥ (B *ᵥ z)) j =
      (G *ᵥ (momentRows (r+1) w c *ᵥ z)) j := by
    rw [Matrix.mulVec_mulVec, hG, Matrix.mulVec_mulVec]
  change (momentRows r w c *ᵥ (U *ᵥ y + B *ᵥ z)) j =
    (G *ᵥ (momentRows (r+1) w c *ᵥ z)) j + (oldRow *ᵥ y) j
  rw [Matrix.mulVec_add, Pi.add_apply, hh, hg, add_comm]

theorem general_tail_moments {q r : ℕ} (hr : r ≤ q+1)
    {A : Matrix ι ι K} {U : Matrix η ι K} {B : Matrix η η K} {w c : η → K}
    (hquad : ∀ j : ℕ, j < q+r+1 → read w c j 1 = 1 / ((j+1 : ℕ) : K))
    (hfeed : ∀ t : FiniteRootedTree, (t.order : ℕ) ≤ q →
      U *ᵥ normalized A t + B *ᵥ (c^((t.order : ℕ)-1)) =
      ((1 / (t.order : K)) : K) • c^(t.order : ℕ))
    (F : GeneralAdjoints q r A U B w c) :
    ∀ (t : FiniteRootedTree) (j : ℕ), (t.order : ℕ)+j ≤ q+r+1 →
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
      let z : Fin r := ⟨j+((t.order : ℕ)-1), by omega⟩
      have hsplit : (u.order : ℕ)+z.val+1 = ((t ◂ u).order : ℕ)+j := by
        dsimp [z]; omega
      rw [low_pure hfeed t ht]
      have hstep : ∀ x : η → K, read w c j (c^((t.order : ℕ)-1) * ((u.order : K) • x)) =
          (u.order : K) * read w c z.val x := by
        intro x
        rw [mul_comm (c^_)]
        change read w c j (((u.order : K) • x)*c^((t.order : ℕ)-1)) = _
        rw [read_times_power]
        simp only [z, read, dotProduct_smul, smul_eq_mul]
      rw [hstep, F.rows]
      have hg : (∑ k : Fin (r+1), F.G z k * read w c k.val
            (tail (normalized (tableau A U B) u))) =
          ∑ k : Fin (r+1), F.G z k * (1 / (((u.order : ℕ)+k.val : ℕ) : K)) := by
        apply Finset.sum_congr rfl
        intro k _
        by_cases hk : z.val+1 < k.val
        · rw [F.gbound z k hk, zero_mul, zero_mul]
        · rw [ihU k.val (by omega)]
      rw [hg, F.old_pay z u (by omega) (by omega)]
      have hscalar := F.scalar z (u.order : ℕ) (by omega) (by omega)
      rw [hsplit] at hscalar
      exact hscalar

/-- Symbolic native ordinary order for a tail of either parity, whenever
there can be at most one attached branch whose size exceeds `q`. -/
theorem general_tail_hasOrder {q r : ℕ} (hr : r ≤ q+1)
    {A : Matrix ι ι K} {U : Matrix η ι K} {B : Matrix η η K} {w c : η → K}
    (hquad : ∀ j : ℕ, j < q+r+1 → read w c j 1 = 1 / ((j+1 : ℕ) : K))
    (hfeed : ∀ t : FiniteRootedTree, (t.order : ℕ) ≤ q →
      U *ᵥ normalized A t + B *ᵥ (c^((t.order : ℕ)-1)) =
      ((1 / (t.order : K)) : K) • c^(t.order : ℕ))
    (F : GeneralAdjoints q r A U B w c) :
    HasOrder (q+r+1) (tableau A U B) (Sum.elim 0 w) := by
  apply normalized_output_eq_order
  intro t ht
  have hw := general_tail_moments hr hquad hfeed F t 0 (by omega)
  simp only [read, row, pow_zero, mul_one, Nat.add_zero] at hw
  simpa [dotProduct, Fintype.sum_sum_type, tail] using hw

/-- A verified old decoder evaluates the chosen integration functional on
the genuine next monomial, even beyond the old paid weighted moments. -/
def frontierRow {q r : ℕ} (D : Matrix (Fin (q+1)) ι K) (H : Fin (r+1) → K) : ι → K :=
  (fun i : Fin (q+1) => ∑ k : Fin (r+1), H k * (1 / ((i.val+k.val+1 : ℕ) : K))) ᵥ* D

theorem frontierRow_pay {q r : ℕ} {A : Matrix ι ι K} {D : Matrix (Fin (q+1)) ι K}
    (hD : IsDecoder A q D) (H : Fin (r+1) → K)
    (t : FiniteRootedTree) (ht : (t.order : ℕ) ≤ q+1) :
    frontierRow D H ⬝ᵥ normalized A t =
      ∑ k : Fin (r+1), H k * (1 / ((((t.order : ℕ)+k.val : ℕ)) : K)) := by
  rw [frontierRow, ← Matrix.dotProduct_mulVec, hD t ht, dotProduct_single, mul_one]
  apply Finset.sum_congr rfl
  intro k _
  have ht' := t.order.pos
  have he : (t.order : ℕ)-1+k.val+1 = (t.order : ℕ)+k.val := by omega
  simp only [he]

/-- A single spare pivot row: earlier rows use old paid weighted moments,
and the last one uses the next-grade decoder. The budget takes the last
row only on trees of size exactly `q+1`. -/
def oneSpareOld {q r : ℕ} (b c : ι → K) (D : Matrix (Fin (q+1)) ι K)
    (H : Matrix (Fin r) (Fin (r+1)) K) : Matrix (Fin r) ι K := fun j =>
  if j.val+1 = r then frontierRow D (H j)
  else H j ᵥ* momentRows (r+1) b c

theorem oneSpare_pay {q r : ℕ} {A : Matrix ι ι K} {b : ι → K}
    {D : Matrix (Fin (q+1)) ι K} (hD : IsDecoder A q D)
    (hA : HasOrder (q+r-1) A b)
    (H : Matrix (Fin r) (Fin (r+1)) K)
    (hH : ∀ j k, j.val+1 < r → j.val ≤ k.val → H j k = 0)
    (j : Fin r) (t : FiniteRootedTree) (hqt : q < (t.order : ℕ))
    (ht : (t.order : ℕ)+j.val+1 ≤ q+r+1) :
    oneSpareOld b (clocks A) D H j ⬝ᵥ normalized A t =
      ∑ k : Fin (r+1), H j k * (1 / ((((t.order : ℕ)+k.val : ℕ)) : K)) := by
  unfold oneSpareOld
  split_ifs with hh
  · exact frontierRow_pay hD (H j) t (by omega)
  · rw [← Matrix.dotProduct_mulVec]
    unfold dotProduct
    apply Finset.sum_congr rfl
    intro k _
    have hj := j.isLt
    by_cases hk : j.val ≤ k.val
    · rw [hH j k (by omega) hk, zero_mul, zero_mul]
    · change H j k * read b (clocks A) k.val (normalized A t) = _
      rw [read_eq_moment, moment hA t k.val (by omega)]

#print axioms general_tail_hasOrder
#print axioms oneSpare_pay
end RKResearch.Certified.TwoOrderMomentTail
