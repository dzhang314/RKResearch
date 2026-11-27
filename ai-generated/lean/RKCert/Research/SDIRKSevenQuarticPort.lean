module

public import RKCert.Research.SDIRKSevenChristoffelScalar
public import Mathlib.Data.ZMod.Basic
import Init.Data.Nat.Bitwise.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! # An engineered early clock in the quartic-pole chart -/

namespace RKResearch.Certified.SDIRKSevenQuarticPort

theorem forced_port_affine {R : Type*} [CommRing R]
    {ga gc aa ac ba bc h : R} (e : (ac-h*bc)*ga-gc*(aa-h*ba)=0) :
    h*(bc*ga-gc*ba)=ac*ga-gc*aa := by
  linear_combination -e

def c3 {R : Type*} [CommRing R] (a b c d t : R) : R :=
  a+b*t+c*t^2+d*t^3

theorem mirrored_ports {R : Type*} [CommRing R] (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ t : R) :
    c3 a₀ a₁ a₂ a₃ t*c3 b₀ b₁ b₂ b₃ (-t)-
      c3 b₀ b₁ b₂ b₃ t*c3 a₀ a₁ a₂ a₃ (-t)=
    2*t*((a₁*b₀-a₀*b₁)+(a₃*b₀-a₂*b₁+a₁*b₂-a₀*b₃)*t^2+
      (a₃*b₂-a₂*b₃)*t^4) := by
  simp only [c3]
  ring

theorem suffix_square {R : Type*} [CommRing R] {u n d : R} (h : (u-2)^2*d=n) :
    n*d=((u-2)*d)^2 := by rw [←h]; ring

open SDIRKSevenChristoffelScalar

def evalMod (q : ℕ) (f : List ℤ) (x : ZMod q) : ZMod q :=
  f.foldr (fun a v => (a : ZMod q)+x*v) 0

def bothSquaresExcluded (q : ℕ) (a b : List ℤ) : Bool :=
  let mask := makeMask (squares q)
  (List.range q).all fun x =>
    !(mask.testBit (evalMod q a (x : ZMod q)).val &&
      mask.testBit (evalMod q b (x : ZMod q)).val)

private theorem mask_hit {l : List ℕ} {i : ℕ} (h : i∈l) :
    (makeMask l).testBit i=true := by
  induction l with
  | nil => simp at h
  | cons j l ih =>
    rw [makeMask,Nat.testBit_or]
    rcases List.mem_cons.mp h with rfl | h'
    · simp [Nat.testBit_shiftLeft]
    · rw [ih h',Bool.or_true]

private theorem square_val {q : ℕ} [NeZero q] (s : ZMod q) :
    (makeMask (squares q)).testBit (s^2).val=true := by
  apply mask_hit
  refine List.mem_map.mpr ⟨s.val,List.mem_range.mpr s.val_lt,?_⟩
  rw [pow_two,ZMod.val_mul]

theorem no_two_squares {q : ℕ} [NeZero q] {a b : List ℤ}
    (h : bothSquaresExcluded q a b=true) (x s t : ZMod q) :
    ¬ (evalMod q a x=s^2 ∧ evalMod q b x=t^2) := by
  rintro ⟨h₁,h₂⟩
  have hh := List.all_eq_true.mp h x.val (List.mem_range.mpr x.val_lt)
  rw [ZMod.natCast_zmod_val,h₁,h₂,square_val,square_val] at hh
  contradiction

def receiptWideU : List ℤ := [32,112,240,156,10,20,90,180,172,28,98,144,202]
def receiptWideQ : List ℤ := [192,184,164,68,33]
def receiptOldU : List ℤ := [12,7,5,17,0,6,16,2,8,5,17,13,5]
def receiptOldQ : List ℤ := [10,12,10,16,3]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
theorem wide_both_charts :
    bothSquaresExcluded 256 receiptWideU receiptWideQ=true ∧
    bothSquaresExcluded 256 receiptWideU.reverse receiptWideQ.reverse=true := by
  decide +kernel

theorem old_both_charts :
    bothSquaresExcluded 19 receiptOldU receiptOldQ=true ∧
    bothSquaresExcluded 19 receiptOldU.reverse receiptOldQ.reverse=true := by
  decide +kernel

end RKResearch.Certified.SDIRKSevenQuarticPort
