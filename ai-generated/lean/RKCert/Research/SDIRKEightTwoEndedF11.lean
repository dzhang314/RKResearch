module

public import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Defs

@[expose] public section

/-! # Literal fourth-row receipt for the F11 two-ended pair census -/

namespace RKResearch.Certified.SDIRKEightTwoEndedF11

local instance : Fact (Nat.Prime 11) := ⟨by decide⟩

abbrev Pair := ℕ × ℕ

structure Corner where
  m : ℕ
  terminalG : ℕ
  u : ℕ
  w : ℕ
  thirdG : ℕ
  reverseU : ℕ
  reverseW : ℕ
  reverseThirdG : ℕ
  other : List Pair

def fourth (u w g₃ x g : ZMod 11) : Bool :=
  let k := 1+2*u-u^2
  let negLin := ((g₃-1/2)/w-(k/2-1/2)/u)/(w-u)
  let lin := (k/2-1/2)/u-negLin*(2+u)
  let off := 1/2-lin-negLin
  let J := off*x+lin*x^2/2+negLin*x^3/3
  let ag := 1+(x-1)/k
  let delta := 4/3+2*(k+1)*(x-1)/(3*k)
  decide (g-(off+lin*x+negLin*x^2)+J-g*(ag-lin-negLin*delta)=0)

def leftGate (c : Corner) (z : Pair) : Bool :=
  fourth c.u c.w c.thirdG z.1 z.2

def rightGate (c : Corner) (z : Pair) : Bool :=
  fourth c.reverseU c.reverseW c.reverseThirdG
    (2*(c.m : ZMod 11)-z.1) (z.2/(2*(c.terminalG : ZMod 11)))

def guard (c : Corner) : Bool :=
  c.other.all fun a => c.other.all fun b =>
    decide (a=b) || !(leftGate c a && rightGate c b)

def corners : List Corner := [
  ⟨2,2,3,10,10,4,9,2,[(1,2),(2,6),(2,9),(3,6)]⟩,
  ⟨2,2,3,10,10,9,4,2,[(1,2),(2,6),(2,9),(3,6)]⟩,
  ⟨2,2,10,3,10,4,9,2,[(1,2),(2,6),(2,9),(3,6)]⟩,
  ⟨2,2,10,3,10,9,4,2,[(1,2),(2,6),(2,9),(3,6)]⟩,
  ⟨2,4,4,9,2,6,7,5,[(1,4),(2,2),(2,10),(3,6)]⟩,
  ⟨2,4,4,9,2,7,6,5,[(1,4),(2,2),(2,10),(3,6)]⟩,
  ⟨2,4,9,4,2,6,7,5,[(1,4),(2,2),(2,10),(3,6)]⟩,
  ⟨2,4,9,4,2,7,6,5,[(1,4),(2,2),(2,10),(3,6)]⟩,
  ⟨2,6,10,9,8,10,9,8,[(1,2),(2,6),(2,9),(3,2)]⟩,
  ⟨2,7,4,9,2,3,10,10,[(1,7),(2,5),(2,7),(3,6)]⟩,
  ⟨2,7,4,9,2,10,3,10,[(1,7),(2,5),(2,7),(3,6)]⟩,
  ⟨2,7,9,4,2,3,10,10,[(1,7),(2,5),(2,7),(3,6)]⟩,
  ⟨2,7,9,4,2,10,3,10,[(1,7),(2,5),(2,7),(3,6)]⟩,
  ⟨2,8,5,8,4,3,10,10,[(1,8),(2,4),(2,10),(3,6)]⟩,
  ⟨2,8,5,8,4,10,3,10,[(1,8),(2,4),(2,10),(3,6)]⟩,
  ⟨2,8,8,5,4,3,10,10,[(1,8),(2,4),(2,10),(3,6)]⟩,
  ⟨2,8,8,5,4,10,3,10,[(1,8),(2,4),(2,10),(3,6)]⟩,
  ⟨2,9,6,7,5,4,9,2,[(1,9),(2,3),(2,4),(3,6)]⟩,
  ⟨2,9,6,7,5,9,4,2,[(1,9),(2,3),(2,4),(3,6)]⟩,
  ⟨2,9,7,6,5,4,9,2,[(1,9),(2,3),(2,4),(3,6)]⟩,
  ⟨2,9,7,6,5,9,4,2,[(1,9),(2,3),(2,4),(3,6)]⟩,
  ⟨2,10,3,10,10,5,8,4,[(1,10),(2,2),(2,3),(3,6)]⟩,
  ⟨2,10,3,10,10,8,5,4,[(1,10),(2,2),(2,3),(3,6)]⟩,
  ⟨2,10,10,3,10,5,8,4,[(1,10),(2,2),(2,3),(3,6)]⟩,
  ⟨2,10,10,3,10,8,5,4,[(1,10),(2,2),(2,3),(3,6)]⟩,
  ⟨3,6,6,1,8,6,1,8,[(3,7),(3,8),(7,2),(10,2)]⟩,
  ⟨5,6,7,3,2,7,3,2,[(3,1),(5,7),(5,8),(7,1)]⟩,
  ⟨7,6,5,8,4,5,8,4,[(1,5),(2,5),(7,2),(7,6)]⟩,
  ⟨7,6,5,8,4,8,5,4,[(1,5),(2,5),(7,2),(7,6)]⟩,
  ⟨7,6,8,5,4,5,8,4,[(1,5),(2,5),(7,2),(7,6)]⟩,
  ⟨7,6,8,5,4,8,5,4,[(1,5),(2,5),(7,2),(7,6)]⟩,
  ⟨8,6,3,10,10,3,10,10,[(2,3),(3,3),(8,2),(8,3)]⟩,
  ⟨8,6,3,10,10,10,3,10,[(2,3),(3,3),(8,2),(8,3)]⟩,
  ⟨8,6,10,3,10,3,10,10,[(2,3),(3,3),(8,2),(8,3)]⟩,
  ⟨8,6,10,3,10,10,3,10,[(2,3),(3,3),(8,2),(8,3)]⟩,
  ⟨9,6,6,7,5,6,7,5,[(1,2),(6,2),(9,1),(9,7)]⟩,
  ⟨9,6,6,7,5,7,6,5,[(1,2),(6,2),(9,1),(9,7)]⟩,
  ⟨9,6,7,6,5,6,7,5,[(1,2),(6,2),(9,1),(9,7)]⟩,
  ⟨9,6,7,6,5,7,6,5,[(1,2),(6,2),(9,1),(9,7)]⟩
]

set_option maxRecDepth 55000 in
set_option maxHeartbeats 14000000 in
theorem finite_receipt : corners.all guard=true := by decide +kernel

theorem no_distinct_fourth_pair {c : Corner} (hc : c∈corners)
    {x y : Pair} (hx : x∈c.other) (hy : y∈c.other) (neq : x≠y) :
    ¬ (leftGate c x=true ∧ rightGate c y=true) := by
  rintro ⟨gx,gy⟩
  have h := List.all_eq_true.mp finite_receipt c hc
  have hh := List.all_eq_true.mp (List.all_eq_true.mp h x hx) y hy
  simp [neq,gx,gy] at hh

end RKResearch.Certified.SDIRKEightTwoEndedF11
