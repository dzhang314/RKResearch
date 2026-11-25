module

public import RKCert.ReviewedNative.FiniteScaledOrderCheck
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.LinearAlgebra.Matrix.Block

@[expose] public section

/-! Sparse storage for the already reviewed integer-scaled evaluator.
Only the matrix action and output are supplied here, with symbolic
proofs against the standard matrix operations. -/

namespace RKResearch.Certified.RationalStrictSDIRKSparseRows

open scoped Matrix

abbrev Row (n : ℕ) := List (Fin n × ℤ)

def entry {n : ℕ} (j : Fin n) : Row n → ℤ
  | [] => 0
  | t :: ts => (if t.1 = j then t.2 else 0) + entry j ts

def rowAct {n : ℕ} (v : Fin n → ℤ) : Row n → ℤ
  | [] => 0
  | t :: ts => t.2 * v t.1 + rowAct v ts

theorem rowAct_eq_dotProduct {n : ℕ} (v : Fin n → ℤ) (ts : Row n) :
    rowAct v ts = (fun j => entry j ts) ⬝ᵥ v := by
  induction ts with
  | nil => simp [rowAct, entry, dotProduct]
  | cons t ts ih =>
    rcases t with ⟨i, a⟩
    change a * v i + rowAct v ts =
      (fun j => (if i = j then a else 0) + entry j ts) ⬝ᵥ v
    rw [ih]
    simp only [dotProduct, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem entry_eq_zero {n : ℕ} (j : Fin n) (ts : Row n)
    (h : ∀ t ∈ ts, t.1 ≠ j) : entry j ts = 0 := by
  revert h
  induction ts with
  | nil => intro _; rfl
  | cons t ts ih =>
    intro h
    have ht : t.1 ≠ j := h t (by simp)
    have hs : ∀ s ∈ ts, s.1 ≠ j := fun s hm => h s (by simp [hm])
    change (if t.1 = j then t.2 else 0) + entry j ts = 0
    rw [if_neg ht, zero_add, ih hs]

def widenIndex {m n : ℕ} (h : m ≤ n) (i : Fin m) : Fin n :=
  ⟨i.val, i.isLt.trans_le h⟩

def widenRow {m n : ℕ} (h : m ≤ n) (d : ℤ) (r : Row m) : Row n :=
  r.map fun t => (widenIndex h t.1, d * t.2)

/-- Scale outside the sparse arithmetic on the shared prefix. -/
theorem rowAct_widenRow {m n : ℕ} (h : m ≤ n) (d : ℤ)
    (v : Fin n → ℤ) (r : Row m) :
    rowAct v (widenRow h d r) = d * rowAct (fun i => v (widenIndex h i)) r := by
  induction r with
  | nil => simp [widenRow, rowAct]
  | cons t r ih =>
    rcases t with ⟨j, a⟩
    change (d * a) * v (widenIndex h j) + rowAct v (widenRow h d r) =
      d * (a * v (widenIndex h j) + rowAct (fun i => v (widenIndex h i)) r)
    rw [ih, mul_add, mul_assoc]

def joinRows {m n : ℕ} (h : m ≤ n) (d : ℤ)
    (headRows : Fin m → Row m) (tailRows : Fin (n - m) → Row n) (i : Fin n) : Row n :=
  if hi : i.val < m then
    widenRow h d (headRows ⟨i.val, hi⟩)
  else
    tailRows ⟨i.val - m, by have ht := i.isLt; omega⟩

def joinAct {m n : ℕ} (h : m ≤ n) (d : ℤ)
    (headRows : Fin m → Row m) (tailRows : Fin (n - m) → Row n)
    (v : Fin n → ℤ) (i : Fin n) : ℤ :=
  if hi : i.val < m then
    d * rowAct (fun j => v (widenIndex h j)) (headRows ⟨i.val, hi⟩)
  else
    rowAct v (tailRows ⟨i.val - m, by have ht := i.isLt; omega⟩)

theorem joinAct_eq_rowAct {m n : ℕ} (h : m ≤ n) (d : ℤ)
    (headRows : Fin m → Row m) (tailRows : Fin (n - m) → Row n)
    (v : Fin n → ℤ) (i : Fin n) :
    joinAct h d headRows tailRows v i = rowAct v (joinRows h d headRows tailRows i) := by
  by_cases hi : i.val < m
  · simp only [joinAct, joinRows, dif_pos hi, rowAct_widenRow]
  · simp only [joinAct, joinRows, dif_neg hi]

def checkFin {n : ℕ} (p : Fin n → Bool) : Bool :=
  (List.finRange n).all p

theorem checkFin_get {n : ℕ} (p : Fin n → Bool) (h : checkFin p = true) (i : Fin n) :
    p i = true :=
  List.all_eq_true.mp h i (List.mem_finRange i)

def lowerCheck {n : ℕ} (rows : Fin n → Row n) : Bool :=
  checkFin fun i => (rows i).all fun t => decide (t.1 ≤ i)

theorem upper_entries_zero_of_check {n : ℕ} (rows : Fin n → Row n)
    (h : lowerCheck rows = true) (i j : Fin n) (hij : i < j) :
    entry j (rows i) = 0 := by
  apply entry_eq_zero
  intro t ht
  have hi := checkFin_get (fun i => (rows i).all fun q => decide (q.1 ≤ i)) h i
  have hle : t.1 ≤ i := of_decide_eq_true (List.all_eq_true.mp hi t ht)
  intro e
  exact (not_le_of_gt hij) (by simpa only [e] using hle)

end RKResearch.Certified.RationalStrictSDIRKSparseRows
