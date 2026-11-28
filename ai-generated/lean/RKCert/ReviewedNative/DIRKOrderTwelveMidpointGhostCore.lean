module
public import Init.Data.Rat.Lemmas

@[expose] public section

/-! Exact arithmetic for the four hidden rows of the fifteen-stage midpoint
DIRK order-twelve tableau. These are normalized by the first live clock. -/

namespace RKResearch.Certified.DIRK12MidpointGhost

def clock (i : Fin 4) : Rat :=
  if i = 0 then 1/4 else if i = 1 then 1/3 else if i = 2 then 8/11 else 1

def tap (i : Fin 4) : Rat :=
  if i = 0 then 256/945 else if i = 1 then 81/520
  else if i = 2 then 161051/393120 else 89/1080

def block (i j : Fin 4) : Rat :=
  if i = 0 then
    if j = 0 then 1/8 else 0
  else if i = 1 then
    if j = 0 then 16/27 else if j = 1 then -5/18 else 0
  else if i = 2 then
    if j = 0 then -128/1331 else if j = 1 then 756/1331 else if j = 2 then 3/22 else 0
  else
    if j = 0 then 880/623 else if j = 1 then -27/26
    else if j = 2 then 43923/64792 else 0

def add4 (f : Fin 4 → Rat) : Rat := f 0 + f 1 + f 2 + f 3
def mul4 (f : Fin 4 → Rat) : Rat := f 0 * f 1 * f 2 * f 3

def act (v : Fin 4 → Rat) (i : Fin 4) : Rat := add4 (fun j => block i j * v j)
def rev (v : Fin 4 → Rat) (i : Fin 4) : Rat := add4 (fun j => block j i * v j)

def cubic (i : Fin 4) : Rat := act (fun j => clock j ^ 2) i - clock i ^ 3 / 3

def barycentric (i : Fin 4) : Rat :=
  tap i * cubic i * mul4 (fun j => if i = j then 1 else clock i - clock j)

theorem clocks_distinct : ∀ i j : Fin 4, i ≠ j → clock i ≠ clock j := by
  decide +kernel

theorem triangular : ∀ i j : Fin 4, i < j → block i j = 0 := by
  decide +kernel

theorem moments : ∀ k : Fin 5,
    add4 (fun i => tap i * clock i ^ (k.val + 1)) = 1 / ((k.val + 2 : Nat) : Rat) := by
  decide +kernel

theorem first_primitive : ∀ i : Fin 4, act clock i = clock i ^ 2 / 2 := by
  decide +kernel

theorem first_adjoint : ∀ i : Fin 4, rev tap i = (1 - clock i) * tap i := by
  decide +kernel

theorem second_adjoint : ∀ i : Fin 4,
    rev (fun j => clock j * tap j) i = (1 - clock i ^ 2) * tap i / 2 := by
  decide +kernel

theorem weighted_cubic_barycentric : ∀ i : Fin 4,
    barycentric i = barycentric 0 ∧ barycentric i ≠ 0 := by
  decide +kernel

end RKResearch.Certified.DIRK12MidpointGhost

#print axioms RKResearch.Certified.DIRK12MidpointGhost.clocks_distinct
#print axioms RKResearch.Certified.DIRK12MidpointGhost.triangular
#print axioms RKResearch.Certified.DIRK12MidpointGhost.moments
#print axioms RKResearch.Certified.DIRK12MidpointGhost.first_primitive
#print axioms RKResearch.Certified.DIRK12MidpointGhost.first_adjoint
#print axioms RKResearch.Certified.DIRK12MidpointGhost.second_adjoint
#print axioms RKResearch.Certified.DIRK12MidpointGhost.weighted_cubic_barycentric
