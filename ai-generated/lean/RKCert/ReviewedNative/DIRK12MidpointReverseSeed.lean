module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! The three actual reverse seed targets, in ascending physical order:
the first occurrence of the double clock, the singleton, and the last
occurrence of the double clock. All amplitudes are normalized by their
target weights and the appropriate closed power of the double clock. -/
namespace RKResearch.Certified.DIRK12MidpointReverse.Seed

open scoped BigOperators

variable {K : Type*} [Field K]

def sigma : K := 1/6
def delta : K := -2*sigma

def lambda (r : K) : K := 3*(r-1)*(r-2)
def k (r : K) : K := (r-1/2)/lambda r
def p (r : K) : K := r^3/(6*(r-1))
def pv (r : K) : K := r/2-p r/r
def aggregate (r : K) : K := 1/2-(delta:K)/(r-1)
def vTap (r : K) : K := (delta:K)/(r*(r-1))
def diag2 (r : K) : K := 1/2+(sigma:K)/(r-1)+k r

def table (r : K) (i j : Fin 3) : K :=
  if i=0 then
    if j=0 then diag2 r else if j=1 then vTap r else aggregate r-diag2 r
  else if i=1 then
    if j=0 then 0 else if j=1 then pv r else p r
  else
    if j=2 then 1/2 else 0

def clock (r : K) (j : Fin 3) : K := if j=1 then r else 1
def pair (j : Fin 3) : K := if j=2 then sigma else if j=0 then -sigma else 0
def bary (r : K) (j : Fin 3) : K :=
  if j=0 then k r*delta else if j=1 then sigma*p r else 0

theorem causal (r : K) {i j : Fin 3} (h : j<i) : table r i j=0 := by
  fin_cases i <;> fin_cases j <;> simp_all [table]

variable [CharZero K]

theorem lambda_nz {r : K} (r1 : r≠1) (r2 : r≠2) : lambda r≠0 :=
  mul_ne_zero (mul_ne_zero (by norm_num) (sub_ne_zero.mpr r1)) (sub_ne_zero.mpr r2)

@[simp] theorem sigma_nz : sigma (K:=K) ≠ 0 := by unfold sigma; norm_num
@[simp] theorem delta_nz : delta (K:=K) ≠ 0 := by unfold delta sigma; norm_num

theorem power1 {r : K} (r0 : r≠0) (r1 : r≠1) (r2 : r≠2) (i : Fin 3) :
    (∑ j : Fin 3, table r i j*clock r j)=(clock r i)^2/2 := by
  have h1 := sub_ne_zero.mpr r1
  have h2 := sub_ne_zero.mpr r2
  fin_cases i <;>
    simp [Fin.sum_univ_three,table,clock,diag2,aggregate,vTap,pv,p,k,lambda,delta,sigma] <;>
    field_simp [r0,h1,h2] <;> ring

theorem power2 {r : K} (r0 : r≠0) (r1 : r≠1) (r2 : r≠2) (i : Fin 3) :
    (∑ j : Fin 3, table r i j*(clock r j)^2)=(clock r i)^3/3+pair i := by
  have h1 := sub_ne_zero.mpr r1
  have h2 := sub_ne_zero.mpr r2
  fin_cases i <;>
    simp [Fin.sum_univ_three,table,clock,diag2,aggregate,vTap,pv,p,k,lambda,delta,sigma,pair] <;>
    field_simp [r0,h1,h2] <;> ring

theorem power3 {r : K} (r0 : r≠0) (r1 : r≠1) (r2 : r≠2) (i : Fin 3) :
    (∑ j : Fin 3, table r i j*(clock r j)^3)=(clock r i)^4/4+(3/2:K)*pair i+lambda r*bary r i := by
  have h1 := sub_ne_zero.mpr r1
  have h2 := sub_ne_zero.mpr r2
  fin_cases i <;>
    simp [Fin.sum_univ_three,table,clock,diag2,aggregate,vTap,pv,p,k,lambda,delta,sigma,pair,bary] <;>
    field_simp [r0,h1,h2] <;> ring

theorem pair_image {r : K} (r0 : r≠0) (r1 : r≠1) (r2 : r≠2) (i : Fin 3) :
    (∑ j : Fin 3, table r i j*pair j)=(1/2:K)*pair i+bary r i := by
  have h1 := sub_ne_zero.mpr r1
  have h2 := sub_ne_zero.mpr r2
  fin_cases i <;>
    simp [Fin.sum_univ_three,table,diag2,aggregate,vTap,pv,p,k,lambda,delta,sigma,pair,bary] <;>
    field_simp [r0,h1,h2] <;> ring

/-- The literal two-way split is the unique one with the specified
aggregate and normalized paired image. -/
def splitSecond (a h : K) : K := (h-sigma*a)/delta
def splitFirst (a h : K) : K := a-splitSecond a h

omit [CharZero K] in
theorem split_aggregate (a h : K) : splitFirst a h+splitSecond a h=a := by
  unfold splitFirst
  ring

theorem split_image (a h : K) : splitFirst a h*(sigma:K)+splitSecond a h*(-sigma)=h := by
  have g := div_mul_cancel₀ (h-(sigma:K)*a) delta_nz
  change splitSecond a h*(-2*sigma)=_ at g
  unfold splitFirst
  linear_combination g

theorem split_unique {a h v1 v2 : K} (e : v1+v2=a)
    (q : v1*(sigma:K)+v2*(-sigma)=h) : v1=splitFirst a h ∧ v2=splitSecond a h := by
  have m : v2*(delta:K)=h-sigma*a := by unfold delta; linear_combination q-sigma*e
  have E : v2=splitSecond a h := (eq_div_iff delta_nz).2 m
  exact ⟨by unfold splitFirst; linear_combination e-E,E⟩

end RKResearch.Certified.DIRK12MidpointReverse.Seed

#print axioms RKResearch.Certified.DIRK12MidpointReverse.Seed.power1
#print axioms RKResearch.Certified.DIRK12MidpointReverse.Seed.power2
#print axioms RKResearch.Certified.DIRK12MidpointReverse.Seed.power3
#print axioms RKResearch.Certified.DIRK12MidpointReverse.Seed.pair_image
#print axioms RKResearch.Certified.DIRK12MidpointReverse.Seed.split_unique
