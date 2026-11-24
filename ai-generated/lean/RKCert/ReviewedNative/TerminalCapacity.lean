module

public import RKCert.ReviewedNative.OddHorizon
public import RKCert.ReviewedNative.GradedPrefix

@[expose] public section

/-! # Saturated reverse room earns an actual terminal
Both the common terminal flag and its zero tail are statements about the
original tableau. A prefix is used only in a separate argument to show
that the last physical weight cannot vanish at the ordinary odd floor.
-/
namespace RKResearch.Certified.Graded.Reverse
open RKResearch Module
open scoped Matrix
noncomputable section
variable {K : Type*} [Field K] {s p j n : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}

/-- Saturated unmarked room forces the first reflected seed to vanish and
identifies the true annihilator, including the all-monomial flag. -/
theorem reverse_capacity_paid (ha : ∀ i j, i ≤ j → A i j = 0)
    (ho : HasOrder A b p) (pay : j+n+2 ≤ p)
    (capacity : s ≤ finrank K (treeSpace A j)+n) :
    firstSeed A b = 0 ∧ back A b n = annih (treeSpace A j) ∧
      primitiveBack A b n = annih (treeSpace A j) := by
  have card := finrank_annih (treeSpace A j)
  rw [Fintype.card_fin] at card
  have low := back_finrank ha ho n (by omega)
  have mono := Submodule.finrank_mono (back_annih ho j n pay)
  have z : firstSeed A b = 0 := by
    by_contra h
    rw [first_dim_one h] at low
    omega
  have exactBack : back A b n = annih (treeSpace A j) :=
    Submodule.eq_of_le_of_finrank_le (back_annih ho j n pay) (by omega)
  have exactPrim : primitiveBack A b n = annih (treeSpace A j) := by
    apply le_antisymm (primitiveBack_annih ho j n pay)
    rw [←exactBack]
    exact back_le_primitiveBack n
  exact ⟨z,exactBack,exactPrim⟩

/-- If the actual reverse space vanishes on a physical coordinate, that
coordinate column belongs to the forward space. -/
theorem coordinate_mem_of_annih_zero (V : Submodule K (Fin s → K)) (t : Fin s)
    (zero : ∀ v ∈ annih V, v t = 0) : coordinate (K:=K) t ∈ V := by
  rw [←annih_annih V]
  apply mem_annih.mpr
  intro v hv
  rw [row_apply,dotProduct_comm,←row_apply,row_coordinate,zero v hv]

/-- An earned last-active node at one and the physical columns of its
entire tail, with no shorter tableau substituted into the conclusion. -/
theorem reverse_capacity_terminal (ha : ∀ i j, i ≤ j → A i j = 0)
    (ho : HasOrder A b p) (pay : j+n+2 ≤ p)
    (capacity : s ≤ finrank K (treeSpace A j)+n)
    {t : Fin s} (term : LastActive b t) :
    firstSeed A b = 0 ∧ nodes A t = 1 ∧ back A b n = annih (treeSpace A j) ∧
      (∀ i, t ≤ i → coordinate (K:=K) i ∈ treeSpace A j) := by
  obtain ⟨hz,backFull,_⟩ := reverse_capacity_paid ha ho pay capacity
  refine ⟨hz,term.node_eq_one ha hz,backFull,?_⟩
  intro i ti
  apply coordinate_mem_of_annih_zero (treeSpace A j) i
  intro v hv
  rw [←backFull] at hv
  exact mem_tailZero.mp (term.back_tail ha hz n hv) i ti

/-- Exact reviewed rooted-tree order on a prefix when the output row is
already zero on every removed stage. -/
theorem prefix_hasOrder_of_suffix_zero (ha : ∀ i j, i ≤ j → A i j = 0)
    (ho : HasOrder A b p) {k : ℕ} (hk : k ≤ s)
    (zero : ∀ i, k ≤ i.val → b i = 0) :
    HasOrder (prefixMatrix A hk) (b ∘ Fin.castLE hk) p := by
  intro t ht
  have weights : (b ∘ Fin.castLE hk) ⬝ᵥ Φ t (prefixMatrix A hk) = b ⬝ᵥ Φ t A := by
    rw [Φ_prefix ha hk,dotProduct,dotProduct]
    exact sum_prefix_zero_tail hk (fun i => b i * Φ t A i)
      (fun i hi => by rw [zero i hi,zero_mul])
  rw [weights]
  exact ho t ht

section Last
variable {m q : ℕ} {T : Matrix (Fin (m+1)) (Fin (m+1)) K}
variable {w : Fin (m+1) → K}

/-- At equality in the ordinary odd floor the final *original*
chronological coordinate is necessarily live. -/
theorem last_weight_of_odd_floor (ha : ∀ i j, i ≤ j → T i j = 0)
    (ho : HasOrder T w p) (q1 : 1 ≤ q) (pay : 2*q+1 ≤ p)
    (floor : m+1 = 3*q) : w (Fin.last m) ≠ 0 := by
  intro z
  have zero (i : Fin (m+1)) (hi : m ≤ i.val) : w i = 0 := by
    have e : i = Fin.last m := Fin.ext (by change i.val = m; have := i.isLt; omega)
    rwa [e]
  let len : m ≤ m+1 := Nat.le_succ m
  have h := prefix_hasOrder_of_suffix_zero ha ho len zero
  have no := odd_midpoint_floor (prefix_strict_lower ha len) h q1 pay
  omega

/-- A directly usable physical last-active certificate at the odd floor. -/
theorem lastActive_of_odd_floor (ha : ∀ i j, i ≤ j → T i j = 0)
    (ho : HasOrder T w p) (q1 : 1 ≤ q) (pay : 2*q+1 ≤ p)
    (floor : m+1 = 3*q) : LastActive w (Fin.last m) := by
  refine ⟨last_weight_of_odd_floor ha ho q1 pay floor,?_⟩
  intro i hi
  exfalso
  change m < i.val at hi
  have := i.isLt
  omega

end Last
end
end RKResearch.Certified.Graded.Reverse
