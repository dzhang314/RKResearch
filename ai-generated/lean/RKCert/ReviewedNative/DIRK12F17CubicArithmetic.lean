module

public import RKCert.ReviewedNative.DualSupport12
public import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Tactic.LinearCombination

@[expose] public section

/-! Three-coordinate reflected arithmetic modulo 17. The kernel-facing
checks run on natural numbers; the soundness proofs evaluate them at a
root of the cubic in an actual commutative ring. -/
namespace RKResearch.Certified.DIRK12F17Cubic

open scoped BigOperators

structure Raw where
  a : Nat
  b : Nat
  c : Nat
  deriving DecidableEq, Inhabited

def num (n : Nat) : Raw := ⟨n%17,0,0⟩

def add (u v : Raw) : Raw := ⟨(u.a+v.a)%17,(u.b+v.b)%17,(u.c+v.c)%17⟩

def mul (u v : Raw) : Raw :=
  let d := u.b*v.c+u.c*v.b
  let e := u.c*v.c
  ⟨(u.a*v.a+7*d+70*e)%17,
   (u.a*v.b+u.b*v.a+14*d+147*e)%17,
   (u.a*v.c+u.b*v.b+u.c*v.a+10*d+114*e)%17⟩

def sub (u v : Raw) : Raw := add u (mul (num 16) v)

def power (u : Raw) : Nat → Raw
  | 0 => num 1
  | k+1 => mul (power u k) u

def csum : {n : Nat} → (Fin n → Raw) → Raw
  | 0, _ => num 0
  | n+1, f => add (f 0) (csum (fun j : Fin n => f j.succ))

section
variable {K : Type*} [CommRing K] [CharP K 17]

def val (z : K) (u : Raw) : K := (u.a:K)+(u.b:K)*z+(u.c:K)*z^2

private theorem cast_mod17 (n : Nat) : ((n%17 : Nat) : K) = (n : K) := by
  have h := congrArg (fun k : Nat => (k:K)) (Nat.mod_add_div n 17)
  rw [Nat.cast_add, Nat.cast_mul, CharP.cast_eq_zero K 17, zero_mul, add_zero] at h
  exact h

@[simp] theorem val_num (z : K) (n : Nat) : val z (num n) = (n:K) := by
  simp [val, num, cast_mod17]

theorem val_add (z : K) (u v : Raw) : val z (add u v) = val z u + val z v := by
  simp only [val, add, cast_mod17, Nat.cast_add]
  ring

def IsCubic (z : K) : Prop := z^3 = 7+14*z+10*z^2

omit [CharP K 17] in
private theorem fourth {z : K} (hz : IsCubic z) :
    z^4 = 70 + 147*z + 114*z^2 := by
  calc
    z^4 = z*z^3 := by ring
    _ = z*(7+14*z+10*z^2) := by rw [show z^3 = _ from hz]
    _ = 7*z+14*z^2+10*z^3 := by ring
    _ = _ := by rw [show z^3 = _ from hz]; ring

theorem val_mul {z : K} (hz : IsCubic z) (u v : Raw) :
    val z (mul u v) = val z u * val z v := by
  have h3 := show z^3 = _ from hz
  have h4 := fourth hz
  simp only [val, mul, cast_mod17, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  linear_combination -((u.b:K)*(v.c:K)+(u.c:K)*(v.b:K))*h3
                     -((u.c:K)*(v.c:K))*h4

theorem val_sub {z : K} (hz : IsCubic z) (u v : Raw) :
    val z (sub u v) = val z u - val z v := by
  rw [sub, val_add, val_mul hz, val_num]
  have h : (16:K) = -1 := by
    apply eq_neg_of_add_eq_zero_left
    calc
      (16:K)+1 = 17 := by ring
      _ = 0 := CharP.cast_eq_zero K 17
  rw [show ((16:Nat):K) = -1 from h, neg_one_mul, sub_eq_add_neg]

theorem val_power {z : K} (hz : IsCubic z) (u : Raw) (n : Nat) :
    val z (power u n) = (val z u)^n := by
  induction n with
  | zero => simp [power]
  | succ n ih => simp only [power, val_mul hz, ih, pow_succ]

theorem val_csum {z : K} {n : Nat} (f : Fin n → Raw) :
    val z (csum f) = ∑ i, val z (f i) := by
  induction n with
  | zero => simp [csum]
  | succ n ih => simp only [csum, val_add, ih, Fin.sum_univ_succ]

end

end RKResearch.Certified.DIRK12F17Cubic
