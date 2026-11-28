module

public import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring

@[expose] public section

/-! Integer polynomial arithmetic with evaluation certificates. Long
division need not trust its quotient choice: each row subtracts a literal
multiple of the modulus. An all-zero result therefore certifies a zero
evaluation at every root of the modulus. -/
namespace RKResearch.Certified.IntegerPolyRootReplay

abbrev ZP := List Int

def add : ZP → ZP → ZP
  | [], ys => ys
  | xs, [] => xs
  | x::xs, y::ys => (x+y)::add xs ys

def scale (r : Int) (p : ZP) : ZP := p.map (fun c => r*c)
def sub (p q : ZP) : ZP := add p (scale (-1) q)
def mul : ZP → ZP → ZP
  | [], _ => []
  | r::rs, q => add (scale r q) (0::mul rs q)

def shift (p : ZP) : Nat → ZP
  | 0 => p
  | j+1 => 0::shift p j

def reduce (modulus : ZP) (degree : Nat) : Nat → ZP → ZP
  | 0, p => p
  | k+1, p =>
    let a := p[k+degree]! / modulus[degree]!
    reduce modulus degree k (sub p (shift (scale a modulus) k))

def zeroed (p : ZP) : Bool := p.all (fun a => decide (a=0))

section
variable {K : Type*} [CommRing K]

def eval : ZP → K → K
  | [], _ => 0
  | r::rs, x => (r:K)+x*eval rs x

theorem eval_add (p q : ZP) (x : K) : eval (add p q) x = eval p x + eval q x := by
  induction p generalizing q with
  | nil => simp [add,eval]
  | cons a p ih =>
    cases q with
    | nil => simp [add,eval]
    | cons b q =>
      simp only [add,eval,ih,Int.cast_add]
      ring

theorem eval_scale (r : Int) (p : ZP) (x : K) :
    eval (scale r p) x = (r:K)*eval p x := by
  induction p with
  | nil => simp [scale,eval]
  | cons a p ih =>
    change ((r*a:Int):K)+x*eval (scale r p) x = (r:K)*((a:K)+x*eval p x)
    rw [Int.cast_mul,ih]
    ring

theorem eval_sub (p q : ZP) (x : K) : eval (sub p q) x = eval p x - eval q x := by
  rw [sub,eval_add,eval_scale]
  simp [sub_eq_add_neg]

theorem eval_mul (p q : ZP) (x : K) : eval (mul p q) x = eval p x*eval q x := by
  induction p with
  | nil => simp [mul,eval]
  | cons a p ih =>
    rw [mul,eval_add,eval_scale,eval,eval,ih]
    push_cast
    ring

theorem eval_shift (p : ZP) (k : Nat) (x : K) : eval (shift p k) x = x^k*eval p x := by
  induction k with
  | zero => simp [shift]
  | succ k ih => simp [shift,eval,ih,pow_succ,mul_comm]; ring

theorem eval_reduce {Q : ZP} {x : K} (root : eval Q x = 0)
    (degree fuel : Nat) (p : ZP) : eval (reduce Q degree fuel p) x = eval p x := by
  induction fuel generalizing p with
  | zero => rfl
  | succ k ih =>
    rw [reduce,ih,eval_sub,eval_shift,eval_scale,root,mul_zero,mul_zero,sub_zero]

theorem eval_zeroed {p : ZP} (h : zeroed p = true) (x : K) : eval p x=0 := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    have hh : decide (a=0) && zeroed p = true := h
    rcases Bool.and_eq_true_iff.mp hh with ⟨hA,hP⟩
    rw [eval,of_decide_eq_true hA,ih hP]
    simp

theorem eval_certified_zero {Q p : ZP} {degree fuel : Nat}
    (h : zeroed (reduce Q degree fuel p)=true) {x : K} (root : eval Q x=0) :
    eval p x=0 := by
  rw [← eval_reduce root degree fuel p]
  exact eval_zeroed h x

end

end RKResearch.Certified.IntegerPolyRootReplay
