module

public import RKCert.ERKGoodPrimeDense
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-! # The computable relative norm

The columns are those of multiplication by the supplied element in the
monic power basis. Conceptually these are the small relative resultants.
The proof checks the actual matrix and uses its ordinary Mathlib determinant.
In particular, the vanishing statement does not require any separability. -/
namespace RKCert.GoodPrimeDense

open Matrix

variable {A R : Type*} [CommRing R]

def sumFin (o : Operations A) : (n : ℕ) → (Fin n → A) → A
  | 0, _ => o.zero
  | n+1, f => o.add (f 0) (sumFin o n (fun i => f i.succ))

def det (o : Operations A) : (n : ℕ) → (Fin n → Fin n → A) → A
  | 0, _ => o.int 1
  | n+1, M => sumFin o (n+1) fun j =>
    let c := M 0 j
    if o.isZero c then o.zero else
      o.mul (pow o (o.int (-1)) j.val)
        (o.mul c (det o n (fun i k => M i.succ (j.succAbove k))))

variable {o : Operations A} {f : A → R} (s : Sound o f)

include s

theorem read_sumFin (n : ℕ) (p : Fin n → A) :
    f (sumFin o n p) = ∑ i, f (p i) := by
  induction n with
  | zero => simp [sumFin, s.zero]
  | succ n ih => simp [sumFin, s.add, ih, Fin.sum_univ_succ]

theorem read_det (n : ℕ) (M : Fin n → Fin n → A) :
    f (det o n M) = (Matrix.of (fun i j => f (M i j))).det := by
  classical
  induction n with
  | zero => simp [det, s.int]
  | succ n ih =>
    rw [det, read_sumFin s, Matrix.det_succ_row_zero]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Matrix.of_apply]
    split
    · rename_i h
      simp [s.zero, s.isZero _ h]
    · rw [s.mul, s.mul, read_pow s, s.int, ih]
      simp only [Int.cast_neg, Int.cast_one]
      rw [← mul_assoc]
      rfl

def coeff (o : Operations A) (p : List A) (i : ℕ) : A := p[i]?.getD o.zero

theorem read_eq_sum (x : R) (n : ℕ) (p : List A) (hp : p.length ≤ n) :
    read f x p = ∑ i : Fin n, x ^ (i : ℕ) * f (coeff o p i) := by
  induction n generalizing p with
  | zero =>
    have h : p = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hp)
    simp [h, read]
  | succ n ih =>
    cases p with
    | nil => simp [coeff, read, s.zero]
    | cons a p =>
      have h : p.length ≤ n := by simp only [List.length_cons] at hp; omega
      rw [Fin.sum_univ_succ]
      simp only [read, Fin.val_zero, coeff, List.getElem?_cons_zero, Option.getD_some,
        pow_zero, one_mul, Fin.val_succ, List.getElem?_cons_succ, pow_succ']
      rw [ih p h, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      simp [coeff,mul_assoc]

def normCol (o : Operations A) (r p : List A) : ℕ → List A
  | 0 => if p.length ≤ r.length then p else reduce o r p
  | j+1 => shift o r (normCol o r p j)

omit s in
theorem normCol_length {r : List A} (hr : 0 < r.length) (p : List A) (j : ℕ) :
    (normCol o r p j).length ≤ r.length := by
  induction j with
  | zero =>
    unfold normCol
    split
    · assumption
    · exact reduce_length hr p
  | succ j ih => exact shift_length ih hr

theorem read_normCol (x : R) {r : List A} (nr : 0 < r.length)
    (hr : read f x r = x ^ r.length) (p : List A) (j : ℕ) :
    read f x (normCol o r p j) = x ^ j * read f x p := by
  induction j with
  | zero =>
    unfold normCol
    split <;> simp [read_reduce s x nr hr]
  | succ j ih =>
    rw [normCol, read_shift s x (normCol_length nr p j) nr hr, ih, pow_succ', mul_assoc]

def norm (o : Operations A) (n : ℕ) (r p : List A) : A :=
  det o n (fun i j => coeff o (normCol o r p j) i)

theorem read_norm_eq_zero [IsDomain R] (x : R) {r : List A} {n : ℕ}
    (nr : 0 < n) (er : r.length = n)
    (hr : read f x r = x ^ n) (p : List A) (zero : read f x p = 0) :
    f (norm o n r p) = 0 := by
  rw [norm, read_det s]
  let M : Matrix (Fin n) (Fin n) R := Matrix.of (fun i j => f (coeff o (normCol o r p j) i))
  change M.det = 0
  let w : Fin n → R := fun i => x ^ i.val
  have rp : 0 < r.length := by omega
  have hr' : read f x r = x ^ r.length := by simpa only [er] using hr
  have eq : w ᵥ* M = 0 := by
    funext j
    change (∑ i : Fin n, x ^ i.val * f (coeff o (normCol o r p j) i)) = 0
    have hl := normCol_length (o:=o) rp p j.val
    rw [er] at hl
    rw [←read_eq_sum s x n _ hl, read_normCol s x rp hr', zero, mul_zero]
  by_contra h
  have z := congrFun (Matrix.eq_zero_of_vecMul_eq_zero h eq) (⟨0, nr⟩ : Fin n)
  simp [w] at z

end RKCert.GoodPrimeDense
