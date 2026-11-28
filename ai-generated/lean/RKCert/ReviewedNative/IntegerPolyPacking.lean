module
public import RKCert.ReviewedNative.IntegerPolyRootReplay
public import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Tactic.LinearCombination

@[expose] public section

/-! Signed integer polynomial packing: one exact integer equality at a
large positive base is injective under an independently checked coefficient
bound. Reflected expression bounds avoid producing dense kernel convolutions. -/
namespace RKResearch.Certified.IntegerPolyRootReplay.Packing

def norm (p : ZP) : Nat := (p.map Int.natAbs).sum

theorem norm_add (p q : ZP) : norm (add p q) ≤ norm p + norm q := by
  induction p generalizing q with
  | nil => simp [norm,add]
  | cons a p ih =>
    cases q with
    | nil => simp [norm,add]
    | cons b q =>
      have h := Nat.add_le_add (Int.natAbs_add_le a b) (ih q)
      simpa only [add,norm,List.map_cons,List.sum_cons,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
        using h

theorem norm_scale (a : Int) (p : ZP) : norm (scale a p) = a.natAbs * norm p := by
  induction p with
  | nil => simp [norm,scale]
  | cons b p ih =>
    change (a*b).natAbs + norm (scale a p) = a.natAbs*(b.natAbs+norm p)
    rw [Int.natAbs_mul,ih,Nat.mul_add]

theorem norm_sub (p q : ZP) : norm (sub p q) ≤ norm p + norm q := by
  rw [sub]
  have h := norm_add p (scale (-1) q)
  rwa [norm_scale,show (-1 : Int).natAbs=1 by decide,one_mul] at h

theorem norm_mul (p q : ZP) : norm (mul p q) ≤ norm p * norm q := by
  induction p with
  | nil => simp [norm,mul]
  | cons a p ih =>
    have h := norm_add (scale a q) (0::mul p q)
    rw [norm_scale] at h
    change norm (add (scale a q) (0::mul p q)) ≤ a.natAbs*norm q+(0+norm (mul p q)) at h
    rw [zero_add] at h
    exact h.trans (by
      change a.natAbs*norm q+norm (mul p q) ≤ (a.natAbs+norm p)*norm q
      rw [Nat.add_mul]
      exact Nat.add_le_add_left ih _)

theorem eval_zero_at_all_of_packed {B : Nat} {p : ZP}
    (hbound : norm p < B) (hpacked : eval p (B:Int)=0) {K : Type*} [CommRing K] (x : K) :
    eval p x=0 := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    change a.natAbs + norm p < B at hbound
    have hp : norm p < B := by omega
    have hab : a.natAbs < B := by omega
    change a + (B:Int)*eval p (B:Int) = 0 at hpacked
    have hz : eval p (B:Int)=0 := by
      by_contra hn
      have e : a = -(B:Int)*eval p (B:Int) := by
        rw [neg_mul]
        exact eq_neg_of_add_eq_zero_left hpacked
      have q : a.natAbs = B * (eval p (B:Int)).natAbs := by
        rw [e,Int.natAbs_mul,Int.natAbs_neg,Int.natAbs_natCast]
      have h1 : 1 ≤ (eval p (B:Int)).natAbs := Int.natAbs_pos.mpr hn
      have h2 : B ≤ a.natAbs := by
        rw [q]
        simpa only [Nat.mul_one] using Nat.mul_le_mul_left B h1
      exact (Nat.not_le_of_lt hab) h2
    have ha : a=0 := by simpa only [hz,mul_zero,add_zero] using hpacked
    rw [eval,ha,ih hp hz]
    simp

inductive Expr
  | atom (p : ZP)
  | plus (u v : Expr)
  | minus (u v : Expr)
  | times (u v : Expr)
  | coeff (a : Int) (u : Expr)

def data : Expr → ZP
  | .atom p => p
  | .plus p q => add (data p) (data q)
  | .minus p q => sub (data p) (data q)
  | .times p q => mul (data p) (data q)
  | .coeff r p => scale r (data p)

def bound : Expr → Nat
  | .atom p => norm p
  | .plus p q | .minus p q => bound p + bound q
  | .times p q => bound p * bound q
  | .coeff r p => r.natAbs * bound p

def read {R : Type*} [CommRing R] (x : R) : Expr → R
  | .atom p => eval p x
  | .plus p q => read x p+read x q
  | .minus p q => read x p-read x q
  | .times p q => read x p*read x q
  | .coeff r p => (r:R)*read x p

theorem data_eval {R : Type*} [CommRing R] (x : R) (p : Expr) :
    eval (data p) x = read x p := by
  induction p <;> simp_all only [data,read,eval_add,eval_sub,eval_mul,eval_scale]

theorem data_bound (p : Expr) : norm (data p) ≤ bound p := by
  induction p with
  | atom p => rfl
  | plus p q hp hq =>
    exact (norm_add (data p) (data q)).trans (Nat.add_le_add hp hq)
  | minus p q hp hq =>
    exact (norm_sub (data p) (data q)).trans (Nat.add_le_add hp hq)
  | times p q hp hq =>
    exact (norm_mul (data p) (data q)).trans (Nat.mul_le_mul hp hq)
  | coeff a p hp =>
    rw [data,bound,norm_scale]
    exact Nat.mul_le_mul_left _ hp

theorem quotient_from_packed {K : Type*} [CommRing K] (x : K) {p : Expr} {Q q : ZP}
    {B : Nat} (root : eval Q x=0)
    (packed : read (B:Int) p = eval Q (B:Int)*eval q (B:Int))
    (small : bound p+norm Q*norm q < B) : read x p=0 := by
  have hn := norm_sub (data p) (mul Q q)
  have b := Nat.add_le_add (data_bound p) (norm_mul Q q)
  have he : eval (sub (data p) (mul Q q)) (B:Int)=0 := by
    rw [eval_sub,data_eval,eval_mul,packed,sub_self]
  have e := eval_zero_at_all_of_packed ((hn.trans b).trans_lt small) he x
  rwa [eval_sub,data_eval,eval_mul,root,zero_mul,sub_zero] at e

end RKResearch.Certified.IntegerPolyRootReplay.Packing
