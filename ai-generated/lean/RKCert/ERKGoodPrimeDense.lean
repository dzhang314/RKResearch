module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.Ring

@[expose] public section

/-! # Executable finite coefficient lists with reflected evaluation

These are certificate data, not a new algebraic hierarchy. The interpretation
is into ordinary Mathlib commutative rings. Each monic reduction is justified
by evaluation at the specified root. -/
namespace RKCert.GoodPrimeDense

structure Operations (A : Type*) where
  zero : A
  int : ℤ → A
  add : A → A → A
  mul : A → A → A
  neg : A → A
  isZero : A → Bool

variable {A R : Type*} [CommRing R]

structure Sound (o : Operations A) (f : A → R) : Prop where
  zero : f o.zero = 0
  int : ∀ a, f (o.int a) = a
  add : ∀ a b, f (o.add a b) = f a + f b
  mul : ∀ a b, f (o.mul a b) = f a * f b
  neg : ∀ a, f (o.neg a) = -f a
  isZero : ∀ a, o.isZero a = true → f a = 0

def scalar (R : Type*) [CommRing R] [DecidableEq R] : Operations R :=
  ⟨0, (↑), (· + ·), (· * ·), (- ·), fun a => decide (a = 0)⟩

theorem Sound.scalar [DecidableEq A] [CommRing A] (f : A →+* R) :
    Sound (scalar A) f :=
  ⟨f.map_zero, map_intCast f, f.map_add, f.map_mul, f.map_neg, fun a h => by
    rw [of_decide_eq_true h, map_zero]⟩

def read (f : A → R) (x : R) : List A → R
  | [] => 0
  | a :: p => f a + x * read f x p

/-- Only remove a highest coefficient known to be zero. -/
def cons (o : Operations A) (a : A) (p : List A) : List A :=
  if p.isEmpty && o.isZero a then [] else a :: p

def constant (o : Operations A) (a : A) : List A := cons o a []

def plus (o : Operations A) : List A → List A → List A
  | [], p => p
  | p, [] => p
  | a :: p, b :: q => cons o (o.add a b) (plus o p q)

def opposite (o : Operations A) : List A → List A
  | [] => []
  | a :: p => cons o (o.neg a) (opposite o p)

def timesScalar (o : Operations A) (a : A) : List A → List A
  | [] => []
  | b :: p => cons o (o.mul a b) (timesScalar o a p)

def times (o : Operations A) : List A → List A → List A
  | [], _ => []
  | a :: p, q => plus o (timesScalar o a q) (cons o o.zero (times o p q))

def isZeroList (o : Operations A) : List A → Bool := fun p => p.all o.isZero

def dense (o : Operations A) : Operations (List A) :=
  ⟨[], fun i => constant o (o.int i), plus o, times o, opposite o, isZeroList o⟩

variable {o : Operations A} {f : A → R} (s : Sound o f) (x : R)

include s

theorem read_cons (a : A) (p : List A) :
    read f x (cons o a p) = f a + x * read f x p := by
  unfold cons
  split
  · rename_i h
    have h₁ := Bool.and_eq_true_iff.mp h
    have z : p = [] := List.length_eq_zero_iff.mp (List.isEmpty_iff_length_eq_zero.mp h₁.1)
    simp [read, z, s.isZero _ h₁.2]
  · rfl

theorem read_constant (a : A) : read f x (constant o a) = f a := by
  simp [constant, read_cons s, read]

theorem read_plus (p q : List A) :
    read f x (plus o p q) = read f x p + read f x q := by
  induction p generalizing q with
  | nil => simp [plus, read]
  | cons a p ih =>
    cases q with
    | nil => simp [plus, read]
    | cons b q =>
      simp only [plus, read_cons s, s.add, read, ih]
      ring

theorem read_opposite (p : List A) :
    read f x (opposite o p) = -read f x p := by
  induction p with
  | nil => simp [opposite, read]
  | cons a p ih => simp only [opposite, read_cons s, s.neg, read, ih]; ring

theorem read_timesScalar (a : A) (p : List A) :
    read f x (timesScalar o a p) = f a * read f x p := by
  induction p with
  | nil => simp [timesScalar, read]
  | cons b p ih => simp only [timesScalar, read_cons s, s.mul, read, ih]; ring

theorem read_times (p q : List A) :
    read f x (times o p q) = read f x p * read f x q := by
  induction p with
  | nil => simp [times, read]
  | cons a p ih =>
    simp only [times, read_plus s, read_timesScalar s, read_cons s, s.zero, zero_add, read, ih]
    ring

theorem read_zeroList (p : List A) (hp : isZeroList o p = true) :
    read f x p = 0 := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    obtain ⟨ha,hp⟩ := Bool.and_eq_true_iff.mp hp
    simp [read, s.isZero _ ha, ih hp]

theorem Sound.dense : Sound (dense o) (read f x) :=
  ⟨rfl, fun _i => (read_constant s _ _).trans (s.int _),
    read_plus s x, read_times s x, read_opposite s x, read_zeroList s x⟩

omit s in
theorem cons_length (a : A) (p : List A) : (cons o a p).length ≤ p.length + 1 := by
  unfold cons
  split <;> simp

omit s in
theorem plus_length (p q : List A) :
    (plus o p q).length ≤ max p.length q.length := by
  induction p generalizing q with
  | nil => simp [plus]
  | cons a p ih =>
    cases q with
    | nil => simp [plus]
    | cons b q =>
      simp only [plus, List.length_cons]
      have h := cons_length (o:=o) (o.add a b) (plus o p q)
      have i := ih q
      omega

omit s in
theorem timesScalar_length (a : A) (p : List A) :
    (timesScalar o a p).length ≤ p.length := by
  induction p with
  | nil => simp [timesScalar]
  | cons b p ih =>
    simp only [timesScalar, List.length_cons]
    exact (cons_length (o:=o) ..).trans (by omega)

omit s in
theorem read_append (f : A → R) (x : R) (p q : List A) :
    read f x (p ++ q) = read f x p + x ^ p.length * read f x q := by
  induction p with
  | nil => simp [read]
  | cons a p ih =>
    simp only [List.cons_append, read, ih, List.length_cons, pow_succ]
    ring

/-- Multiply by the variable using the *negative* lower coefficients of
the monic relation. -/
def shift (o : Operations A) (r p : List A) : List A :=
  if p.length < r.length then cons o o.zero p
  else plus o (cons o o.zero p.dropLast) (timesScalar o (p.getLastD o.zero) r)

omit s in
theorem shift_length {r p : List A} (h : p.length ≤ r.length) (nr : 0 < r.length) :
    (shift o r p).length ≤ r.length := by
  unfold shift
  split
  · exact (cons_length (o:=o) ..).trans (by omega)
  · apply (plus_length ..).trans
    apply max_le
    · apply (cons_length (o:=o) ..).trans
      simp only [List.length_dropLast]
      omega
    · exact timesScalar_length ..

theorem read_shift {r p : List A} (h : p.length ≤ r.length) (nr : 0 < r.length)
    (hr : read f x r = x ^ r.length) :
    read f x (shift o r p) = x * read f x p := by
  unfold shift
  split
  · simp [read_cons s, s.zero]
  · rename_i hn
    have hp : p ≠ [] := by
      intro e
      simp only [e, List.length_nil] at hn
      omega
    have e : p.dropLast ++ [p.getLast hp] = p := List.dropLast_concat_getLast hp
    have eq : read f x p =
        read f x p.dropLast + x ^ p.dropLast.length * f (p.getLast hp) := by
      nth_rw 1 [←e]
      rw [read_append]
      simp [read]
    have er : r.length = p.dropLast.length+1 := by simp; omega
    simp only [read_plus s, read_cons s, s.zero, zero_add, read_timesScalar s, hr,
      List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hp, Option.getD_some]
    rw [eq, er, pow_succ]
    ring

def reduce (o : Operations A) (r : List A) : List A → List A
  | [] => []
  | a :: p => plus o (constant o a) (shift o r (reduce o r p))

omit s in
theorem reduce_length {r : List A} (nr : 0 < r.length) (p : List A) :
    (reduce o r p).length ≤ r.length := by
  induction p with
  | nil => simp [reduce]
  | cons a p ih =>
    apply (plus_length ..).trans
    apply max_le
    · exact (cons_length ..).trans (by simp; omega)
    · exact shift_length ih nr

theorem read_reduce {r : List A} (nr : 0 < r.length)
    (hr : read f x r = x ^ r.length) (p : List A) :
    read f x (reduce o r p) = read f x p := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp only [reduce, read_plus s, read_constant s, read_shift s x (reduce_length nr p) nr hr, read, ih]

def quotient (o : Operations A) (r : List A) : Operations (List A) :=
  { dense o with mul := fun p q => reduce o r (times o p q) }

theorem Sound.quotient {r : List A} (nr : 0 < r.length)
    (hr : read f x r = x ^ r.length) :
    Sound (quotient o r) (read f x) where
  __ := s.dense x
  mul := fun p q => (read_reduce s x nr hr _).trans (read_times s x p q)

def generator (o : Operations A) : List A := [o.zero, o.int 1]

theorem read_generator : read f x (generator o) = x := by
  simp [generator, read, s.zero, s.int]

def pow (o : Operations A) (a : A) : ℕ → A
  | 0 => o.int 1
  | n+1 => o.mul (pow o a n) a

theorem read_pow (a : A) (n : ℕ) : f (pow o a n) = f a ^ n := by
  induction n with
  | zero => simp [pow, s.int]
  | succ n ih => simp [pow, s.mul, ih, pow_succ]

end RKCert.GoodPrimeDense
