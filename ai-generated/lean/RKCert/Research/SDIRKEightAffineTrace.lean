module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Affine chronology and exact prime-support receipts at three distinct physical zeros -/

namespace RKResearch.Certified.SDIRKEightAffineTrace

theorem arithmetic_factor {R : Type*} [CommRing R] (u : R) :
    (-2+u+4*u^2-u^3)-2*(3*u-2) = -((u-1)^2*(u-2)) := by ring

theorem exchanged_affine_root {R : Type*} [CommRing R] {u v : R} :
    (1-u)*(2-v)+(1-v)*(2-u)=4-3*(u+v)+2*u*v := by ring

theorem null_prime_support :
    Nat.gcd 1016064000000 849674=14 ∧
    Nat.gcd 848931890625 917773=1 := by decide +kernel

theorem affine_prime_support :
    Nat.gcd 590713 2195891=1 ∧
    Nat.gcd (Nat.gcd 442659953786344729677 2426138581130786239123999329)
      21483260063623790691729363=81 := by decide +kernel

end RKResearch.Certified.SDIRKEightAffineTrace
