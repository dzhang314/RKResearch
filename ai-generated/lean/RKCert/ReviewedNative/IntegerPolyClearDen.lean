module
public import RKCert.ReviewedNative.IntegerPolyRootReplay
public import RKCert.ReviewedNative.DirectedRatBox
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

@[expose] public section

/-! Clear a common denominator on a list of rational coefficients while
preserving its actual Horner value over a characteristic-zero field. -/
namespace RKResearch.Certified.IntegerPolyRootReplay

open DirectedRatBox

def clearDen (D : Nat) (cs : List ℚ) : ZP :=
  cs.map fun q => q.num * ((D / q.den : Nat) : Int)

section
variable {K : Type*} [Field K] [CharZero K]

theorem cast_clearDen_atom (D : Nat) (q : ℚ) (h : q.den ∣ D) :
    (((q.num * ((D/q.den : Nat) : Int)):Int):K) = (D:K)*(q:K) := by
  have denNZ : (q.den:K) ≠ 0 := Nat.cast_ne_zero.mpr q.den_nz
  have hc := congrArg (fun k : Nat => (k:K)) (Nat.div_mul_cancel h)
  rw [Nat.cast_mul] at hc
  rw [Int.cast_mul,Int.cast_natCast,Rat.cast_def]
  field_simp [denNZ]
  linear_combination (q.num:K)*hc

theorem eval_clearDen (D : Nat) (cs : List ℚ) (x : K) (h : ∀ q ∈ cs, q.den ∣ D) :
    eval (clearDen D cs) x = (D:K)*ratHorner cs x := by
  induction cs with
  | nil => simp [clearDen,eval,ratHorner,horner]
  | cons q qs ih =>
    have hq := h q (by simp)
    have hr := ih (fun r hr => h r (by simp [hr]))
    change (((q.num * ((D/q.den:Nat):Int)):Int):K) +
        x*eval (clearDen D qs) x = (D:K)*((q:K)+x*ratHorner qs x)
    rw [cast_clearDen_atom D q hq,hr]
    ring

theorem cubic_transfer_of_three {d f f0 f1 f2 r0 r1 r2 r3 : K}
    (hd : d ≠ 0) (hr : f0+f1*f+f2*f^2+d*f^3=0)
    (h0 : d*r0-r3*f0=0) (h1 : d*r1-r3*f1=0) (h2 : d*r2-r3*f2=0) :
    r0+r1*f+r2*f^2+r3*f^3=0 := by
  apply (mul_eq_zero.mp (show d*(r0+r1*f+r2*f^2+r3*f^3)=0 by
    linear_combination h0+f*h1+f^2*h2+r3*hr)).resolve_left hd

end

end RKResearch.Certified.IntegerPolyRootReplay
