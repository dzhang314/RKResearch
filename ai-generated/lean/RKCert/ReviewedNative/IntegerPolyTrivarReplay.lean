module

public import RKCert.ReviewedNative.IntegerPolyBivarReplay
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! Pack a literal integer trivariate gate after substituting two
denominator-homogenized univariate polynomials. -/
namespace RKResearch.Certified.IntegerPolyRootReplay.Packing

structure TrivarTerm where
  i : Nat
  j : Nat
  k : Nat
  c : Int

def trivar {K : Type*} [CommRing K] (l : List TrivarTerm) (x y t : K) : K :=
  match l with
  | [] => 0
  | a::as => (a.c:K)*x^a.i*y^a.j*t^a.k+trivar as x y t

def trivarClear (dy dt ny nt : Nat) (l : List TrivarTerm) (Y T : ZP) : Expr :=
  match l with
  | [] => .atom []
  | a::as =>
    .plus
      (.coeff a.c (.times
        (.times (epow (.atom [(dy:Int)]) (ny-a.j)) (epow (.atom [(dt:Int)]) (nt-a.k)))
        (.times (epow (.atom [0,1]) a.i) (.times (epow (.atom Y) a.j) (epow (.atom T) a.k)))))
      (trivarClear dy dt ny nt as Y T)

theorem read_trivarClear {K : Type*} [CommRing K] (x y t : K) (dy dt ny nt : Nat)
    (l : List TrivarTerm) (Y T : ZP) (hy : eval Y x=(dy:K)*y) (ht : eval T x=(dt:K)*t)
    (hd : ∀ a∈l, a.j≤ny ∧ a.k≤nt) :
    read x (trivarClear dy dt ny nt l Y T) = (dy:K)^ny*(dt:K)^nt*trivar l x y t := by
  induction l with
  | nil => simp [trivarClear,read,eval,trivar]
  | cons a as ih =>
    obtain ⟨ay,az⟩ := hd a (by simp)
    have tail : ∀ b∈as, b.j≤ny ∧ b.k≤nt := fun b hb => hd b (by simp [hb])
    simp only [trivarClear,trivar,read,read_epow,eval,Int.cast_natCast,Int.cast_zero,
      Int.cast_one,mul_zero,add_zero,zero_add,mul_one,hy,ht,ih tail,mul_pow]
    have py : (dy:K)^(ny-a.j)*(dy:K)^a.j=(dy:K)^ny := by
      rw [← pow_add,Nat.sub_add_cancel ay]
    have pt : (dt:K)^(nt-a.k)*(dt:K)^a.k=(dt:K)^nt := by
      rw [← pow_add,Nat.sub_add_cancel az]
    have z : ((dy:K)^(ny-a.j)*(dt:K)^(nt-a.k))*((dy:K)^a.j*(dt:K)^a.k) =
        (dy:K)^ny*(dt:K)^nt := by
      calc
        _ = ((dy:K)^(ny-a.j)*(dy:K)^a.j)*((dt:K)^(nt-a.k)*(dt:K)^a.k) := by ring
        _ = _ := by rw [py,pt]
    linear_combination ((a.c:K)*x^a.i*y^a.j*t^a.k)*z

end RKResearch.Certified.IntegerPolyRootReplay.Packing

#print axioms RKResearch.Certified.IntegerPolyRootReplay.Packing.read_trivarClear
