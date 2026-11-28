module

public import RKCert.ReviewedNative.IntegerPolyPacking
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

@[expose] public section

/-! Denominator-homogenized bivariate polynomial evaluation with an
integer-polynomial substitution. No polynomial quotient is trusted. -/
namespace RKResearch.Certified.IntegerPolyRootReplay.Packing

structure BivarTerm where
  i : Nat
  j : Nat
  c : Int

def bivar {K : Type*} [CommRing K] (l : List BivarTerm) (x y : K) : K :=
  match l with
  | [] => 0
  | t::ts => (t.c:K)*x^t.i*y^t.j+bivar ts x y

def epow (p : Expr) : Nat → Expr
  | 0 => .atom [1]
  | n+1 => .times p (epow p n)

theorem read_epow {K : Type*} [CommRing K] (x : K) (p : Expr) (n : Nat) :
    read x (epow p n)=(read x p)^n := by
  induction n with
  | zero => simp [epow,read,eval]
  | succ n ih => simp [epow,read,ih,pow_succ']

def bivarClear (d n : Nat) (l : List BivarTerm) (Y : ZP) : Expr :=
  match l with
  | [] => .atom []
  | t::ts =>
    .plus
      (.coeff t.c
        (.times (epow (.atom [(d:Int)]) (n-t.j))
          (.times (epow (.atom [0,1]) t.i) (epow (.atom Y) t.j))))
      (bivarClear d n ts Y)

theorem read_bivarClear {K : Type*} [CommRing K] (x y : K) (d n : Nat)
    (l : List BivarTerm) (Y : ZP)
    (hy : eval Y x=(d:K)*y) (hn : ∀ t∈l, t.j≤n) :
    read x (bivarClear d n l Y)=(d:K)^n*bivar l x y := by
  induction l with
  | nil => simp [bivarClear, read,eval,bivar]
  | cons t ts ih =>
    have ht : t.j≤n := hn t (by simp)
    have hts : ∀ u∈ts, u.j≤n := fun u hu => hn u (by simp [hu])
    simp only [bivarClear,bivar,read,read_epow,eval,Int.cast_natCast,Int.cast_zero,
      Int.cast_one,mul_zero,add_zero,zero_add,mul_one,hy,ih hts,mul_pow]
    have p : (d:K)^(n-t.j)*(d:K)^t.j=(d:K)^n := by
      rw [← pow_add,Nat.sub_add_cancel ht]
    linear_combination ((t.c:K)*x^t.i*y^t.j)*p

end RKResearch.Certified.IntegerPolyRootReplay.Packing

#print axioms RKResearch.Certified.IntegerPolyRootReplay.Packing.read_bivarClear
