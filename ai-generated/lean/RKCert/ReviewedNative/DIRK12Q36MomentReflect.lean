module
public import RKCert.ReviewedNative.IntegerPolyPacking
public import RKCert.ReviewedNative.IntegerPolyClearDen
public import RKCert.ReviewedNative.DIRK12MidpointRealStarBridge
import Mathlib.Tactic.LinearCombination

@[expose] public section

/-! Integer homogeneous moment expressions for a sequence of scaled nodal
roots, with explicit grade budget. This connects the reflected coefficient
arrays to unit-interval polynomial moments instead of sampling the roots. -/
namespace RKResearch.Certified.DIRK12Q36Moments.MomentReflect

open IntegerPolyRootReplay IntegerPolyRootReplay.Packing
open DIRK12MidpointRealInterval DirectedRatBox Polynomial
open scoped Polynomial

abbrev Input := List (Nat×Expr)

def lcmScalar : Nat := 27720

def momentExpr : Input → Nat → Expr
  | [], j => .atom [((lcmScalar/(j+1):Nat):Int)]
  | s::ss, j => .minus (.coeff (s.1:Int) (momentExpr ss (j+1)))
      (.times s.2 (momentExpr ss j))

def denom : Input → Nat
  | [] => lcmScalar
  | a::as => a.1*denom as

theorem lcm_dvd : ∀ j : Fin 12, j.val+1 ∣ lcmScalar := by decide +kernel

section
variable {K : Type*} [Field K] [CharZero K]

theorem read_moment {x : K} {xs : Input} {rr : List K}
    (fits : List.Forall₂ (fun f r => read x f.2 = (f.1:K)*r) xs rr)
    (j : Nat) (paid : j+xs.length < 12) :
    read x (momentExpr xs j) = (denom xs:K)*moment rr j := by
  induction fits generalizing j with
  | nil =>
    have hj : j<12 := by simpa using paid
    have h := congrArg (fun k : Nat => (k:K)) (Nat.div_mul_cancel (lcm_dvd ⟨j,hj⟩))
    rw [Nat.cast_mul] at h
    simp only [momentExpr,Packing.read,IntegerPolyRootReplay.eval,Int.cast_natCast,mul_zero,add_zero,denom,moment]
    rw [Rat.cast_div,Rat.cast_one,Rat.cast_natCast,mul_one_div]
    have u : ((j+1:Nat):K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    exact (eq_div_iff u).mpr h
  | @cons t r xs rr ht hs ih =>
    have pj : j+xs.length < 12 := by simp only [List.length_cons] at paid; omega
    have pk : j+1+xs.length < 12 := by simp only [List.length_cons] at paid; omega
    simp only [momentExpr,Packing.read,Int.cast_natCast,denom,moment]
    rw [ih (j+1) pk,ih j pj,ht,Nat.cast_mul]
    ring

def firstSix (x : K) : List K :=
  let a := ((1/2 : ℚ) : K)
  [0,1,a,1-a*x,1-a*(ratHorner yCoeffs x),1-a*(ratHorner tCoeffs x)]

theorem last_moment (x f : K) (j : Nat) :
    moment (fixed x f) j = moment (firstSix x) (j+1)-moment (firstSix x) j+
      f*moment (firstSix x) j := by
  have hv : fixed x f=firstSix x++[1-f] := rfl
  have eq : hull (fixed x f)=hull ((1-f)::firstSix x) := by
    rw [hv,hull_append,hull,hull,hull,mul_one,mul_comm]
  have h : moment (fixed x f) j = moment ((1-f)::firstSix x) j := by
    rw [← integral_hull,← integral_hull,eq]
  rw [h,moment]
  ring

theorem affine_read {x : K} {xs : Input}
    (fits : List.Forall₂ (fun f r => read x f.2 = (f.1:K)*r) xs (firstSix x))
    (j : Nat) (paid : j+1+xs.length < 12) (f : K) :
    read x (.minus (momentExpr xs (j+1)) (momentExpr xs j)) +
      f*read x (momentExpr xs j) = (denom xs:K)*moment (fixed x f) j := by
  rw [Packing.read,last_moment,read_moment fits (j+1) paid,read_moment fits j (by omega)]
  ring

end

end RKResearch.Certified.DIRK12Q36Moments.MomentReflect
