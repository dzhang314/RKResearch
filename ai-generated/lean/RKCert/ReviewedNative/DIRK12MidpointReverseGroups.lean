module

public import RKCert.ReviewedNative.DIRK12MidpointReverseSeed
public import RKCert.ReviewedNative.PositiveCardinalRead
import Mathlib.Tactic.LinearCombination

@[expose] public section

/-! Three signed grouped returns, then a literal four-row paid split.
The known chronology is charged to the target before interpolation.
No positive-degree moment at a repeated physical site is double counted. -/
namespace RKResearch.Certified.DIRK12MidpointReverse.Groups

open scoped BigOperators
variable {K : Type*} [Field K] [CharZero K]

/-- Group order is d, v, u. The true return order will be u,d₂,v,d₁. -/
def clock (r t : K) (j : Fin 3) : K := if j=0 then 1 else if j=1 then r else t
def sourceClock (r t : K) (j : Fin 4) : K := if j=0 then t else if j=2 then r else 1

theorem clock_guards {r t : K}
    (r0 : r≠0) (t0 : t≠0) (r1 : r≠1) (t1 : t≠1) (tr : t≠r) :
    Function.Injective (clock r t) ∧ ∀ j, clock r t j≠0 := by
  constructor
  · intro i j e
    fin_cases i <;> fin_cases j <;> simp_all [clock,eq_comm]
  · intro i
    fin_cases i <;> simp_all [clock]

def demand (r z h : K) (past : Fin 3 → K) (j : Fin 3) : K :=
  z^(j.val+2)/((j.val+2:Nat):K)+(if j=2 then Seed.lambda r*h else 0)-past j

noncomputable def weight (r t z h : K) (past : Fin 3 → K) :=
  PositiveCardinalRead.weights (clock r t) (demand r z h past)

noncomputable def table (r t z h : K) (past : Fin 3 → K) (j : Fin 4) : K :=
  let w := weight r t z h past
  if j=0 then w 2 else if j=1 then Seed.splitSecond (w 0) h
  else if j=2 then w 1 else Seed.splitFirst (w 0) h

theorem table_reads {r t : K}
    (inj : Function.Injective (clock r t)) (nz : ∀ j, clock r t j≠0)
    (z h : K) (past : Fin 3 → K) (j : Fin 3) :
    past j+(∑ i : Fin 4, table r t z h past i*(sourceClock r t i)^(j.val+1)) =
      z^(j.val+2)/((j.val+2:Nat):K)+(if j=2 then Seed.lambda r*h else 0) := by
  have eq := PositiveCardinalRead.recovers _ inj nz (demand r z h past) j
  change (∑ i : Fin 3, weight r t z h past i*(clock r t i)^(j.val+1))=_ at eq
  rw [Fin.sum_univ_three,demand] at eq
  rw [Fin.sum_univ_four]
  simp only [clock,sourceClock,table,show (2:Fin 3)≠0 by decide,
    show (2:Fin 3)≠1 by decide,show (1:Fin 3)≠0 by decide,
    show (1:Fin 4)≠0 by decide,show (1:Fin 4)≠2 by decide, show (2:Fin 4)≠0 by decide,
    show (2:Fin 4)≠1 by decide,show (3:Fin 4)≠0 by decide,
    show (3:Fin 4)≠1 by decide,show (3:Fin 4)≠2 by decide,
    ite_true,ite_false,one_pow,mul_one] at eq ⊢
  have spl := Seed.split_aggregate (weight r t z h past 0) h
  linear_combination eq+spl

theorem table_pair (r t z h : K) (past : Fin 3 → K) :
    table r t z h past 3*(Seed.sigma:K)+table r t z h past 1*(-Seed.sigma)=h := by
  have e := Seed.split_image (weight r t z h past 0) h
  simpa only [table, show (3:Fin 4)≠0 by decide,show (3:Fin 4)≠1 by decide,
    show (3:Fin 4)≠2 by decide,show (1:Fin 4)≠0 by decide,ite_false,ite_true] using e

end RKResearch.Certified.DIRK12MidpointReverse.Groups

#print axioms RKResearch.Certified.DIRK12MidpointReverse.Groups.clock_guards
#print axioms RKResearch.Certified.DIRK12MidpointReverse.Groups.table_reads
#print axioms RKResearch.Certified.DIRK12MidpointReverse.Groups.table_pair
