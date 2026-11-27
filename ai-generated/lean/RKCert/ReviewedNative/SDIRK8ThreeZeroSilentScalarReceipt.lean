module

public import RKCert.ReviewedNative.SDIRK8TwoZeroLineScalarReceipt
public import Mathlib.Algebra.CharZero.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8ThreeZeroSilentScalarReceipt

open RKCert.ReviewedNative.DyadicBox64
open RKCert.ReviewedNative.SDIRK8TwoZeroLineScalarReceipt (rootBox rootBox_opposite_signs)

inductive Expr
  | first | second | num : ℚ → Expr
  | add : Expr → Expr → Expr
  | sub : Expr → Expr → Expr
  | mul : Expr → Expr → Expr

def value {K : Type*} [Field K] (d z : K) : Expr → K
  | .first => d
  | .second => z
  | .num n => n
  | .add a b => value d z a + value d z b
  | .sub a b => value d z a - value d z b
  | .mul a b => value d z a * value d z b

private def bound (A B : Box) : Expr → Box
  | .first => A
  | .second => B
  | .num n => point n
  | .add a b => add (bound A B a) (bound A B b)
  | .sub a b => sub (bound A B a) (bound A B b)
  | .mul a b => mul (bound A B a) (bound A B b)

private theorem bound_sound {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {A B : Box} {d z : K} (ha : encloses A d) (hb : encloses B z) (e : Expr) :
    encloses (bound A B e) (value d z e) := by
  induction e with
  | first => exact ha
  | second => exact hb
  | num n => exact point_encloses n
  | add a b sa sb => exact add_encloses sa sb
  | sub a b sa sb => exact sub_encloses sa sb
  | mul a b sa sb => exact mul_encloses sa sb

local notation "Qₑ" => Expr.num
local infixl:65 " +ₑ " => Expr.add
local infixl:65 " -ₑ " => Expr.sub
local infixl:70 " *ₑ " => Expr.mul

private def lineExpr : Expr :=
  let d := Expr.first
  let z := Expr.second
  (Qₑ 1 -ₑ z *ₑ z) *ₑ Qₑ (1/2) -ₑ d *ₑ (Qₑ 1 -ₑ z) -ₑ (Qₑ 1 -ₑ d) *ₑ (z -ₑ d)

private def endChart : List (Expr × Expr) :=
  let d := Expr.first
  [(Qₑ 1 -ₑ d, d), (Qₑ 1 -ₑ d, Qₑ 1 -ₑ d), (Qₑ (1/2), Qₑ (1/2)),
   (Qₑ 4 -ₑ Qₑ 5 *ₑ d, Qₑ 1 -ₑ d), (Qₑ 3 *ₑ d -ₑ Qₑ 1, Qₑ 1 -ₑ d),
   (Qₑ (1/2), Qₑ 1 -ₑ d),
   ((Qₑ 4 -ₑ d) *ₑ Qₑ (1/5), (Qₑ 1 +ₑ d) *ₑ Qₑ (1/5)),
   ((Qₑ 1 +ₑ d) *ₑ Qₑ (1/3), (Qₑ 2 -ₑ d) *ₑ Qₑ (1/3))]

private def quadExpr (pair : Expr × Expr) : Expr :=
  let (e,g) := pair
  let d := Expr.first
  let z := Expr.second
  (Qₑ 1 -ₑ z *ₑ z *ₑ z) *ₑ Qₑ (1/3) -ₑ
    (d +ₑ e) *ₑ (Qₑ 1 -ₑ z *ₑ z) *ₑ Qₑ (1/2) +ₑ
    d *ₑ e *ₑ (Qₑ 1 -ₑ z) -ₑ g *ₑ (z -ₑ d) *ₑ (z -ₑ e)

private def avoidsZero (i j : Fin 4) (e : Expr) : Bool :=
  let B := bound (rootBox i) (rootBox j) e
  decide (B.hi < 0 ∨ 0 < B.lo)

private def tests : List Expr := lineExpr :: endChart.map quadExpr

private def check (i j : Fin 4) : Bool :=
  if i=j then true else tests.all (avoidsZero i j)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem checks (i j : Fin 4) : check i j = true := by
  fin_cases i <;> fin_cases j <;> decide +kernel

private theorem checked {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {d z : K} {i j : Fin 4} (hd : encloses (rootBox i) d) (hz : encloses (rootBox j) z)
    (hij : i≠j) {e : Expr} (he : e ∈ tests) : value d z e ≠ 0 := by
  have hall : tests.all (avoidsZero i j) = true := by simpa [check,hij] using checks i j
  have hs := List.all_eq_true.mp hall e he
  have hi : (bound (rootBox i) (rootBox j) e).hi < 0 ∨
      0 < (bound (rootBox i) (rootBox j) e).lo := by simpa [avoidsZero] using hs
  rcases hi with hi|hi
  · exact (sign_neg (bound_sound hd hz e) hi).ne
  · exact (sign_pos (bound_sound hd hz e) hi).ne'

/-- The reflected linear primitive minus literal diagonal value. -/
def lineGate {K : Type*} [Field K] (d z : K) : K :=
  (1-z*z)*(1/2)-d*(1-z)-(1-d)*(z-d)

/-- The eight chronological candidates (other active clock, diagonal). -/
def clockCandidates {K : Type*} [Field K] (d : K) : List (K × K) :=
  [(1-d,d), (1-d,1-d), (1/2,1/2), (4-5*d,1-d), (3*d-1,1-d), (1/2,1-d),
   ((4-d)*(1/5),(1+d)*(1/5)), ((1+d)*(1/3),(2-d)*(1/3))]

/-- The eight-case list is exhaustive once the first three physical
clocks have exhausted the two active sites and the one silent site. -/
theorem clockCandidates_of_chronology {K : Type*} [Field K] [CharZero K]
    (d e g x y : K)
    (hd : d+d ≠ 1)
    (hterm : 1-g=d ∨ 1-g=e)
    (hfront : g=d ∨ g=e ∨ (x=d ∧ y=e) ∨ (x=e ∧ y=d))
    (hrow : y+x=4*g ∨ y=2*x-g) :
    (e,g) ∈ clockCandidates d := by
  rcases hfront with hfirst|hfirst|⟨hx,hy⟩|⟨hx,hy⟩
  · rw [hfirst] at hterm ⊢
    rcases hterm with ht|ht
    · exact (hd (by linear_combination -ht)).elim
    · rw [←ht]
      simp [clockCandidates]
  · rw [hfirst] at hterm ⊢
    rcases hterm with ht|ht
    · have h : e=1-d := by linear_combination -ht
      rw [h]
      simp [clockCandidates]
    · have h : e=(1/2:K) := by linear_combination -(1/2:K)*ht
      rw [h]
      simp [clockCandidates]
  · rw [hx,hy] at hrow
    rcases hterm with ht|ht
    · have hg : g=1-d := by linear_combination -ht
      rw [hg] at hrow ⊢
      rcases hrow with h|h
      · have he : e=4-5*d := by linear_combination h
        rw [he]
        simp [clockCandidates]
      · have he : e=3*d-1 := by linear_combination h
        rw [he]
        simp [clockCandidates]
    · rw [←ht] at hrow ⊢
      rcases hrow with h|h
      · have hg : g=(1+d)*(1/5) := by linear_combination -(1/5:K)*h
        rw [hg]
        have he : 1-(1+d)*(1/5)=(4-d)*(1/5) := by ring
        rw [he]
        simp [clockCandidates]
      · exact (hd (by linear_combination -h)).elim
  · rw [hx,hy] at hrow
    rcases hterm with ht|ht
    · have hg : g=1-d := by linear_combination -ht
      rw [hg] at hrow ⊢
      rcases hrow with h|h
      · have he : e=4-5*d := by linear_combination h
        rw [he]
        simp [clockCandidates]
      · have he : e=(1/2:K) := by linear_combination -(1/2:K)*h
        rw [he]
        simp [clockCandidates]
    · rw [←ht] at hrow ⊢
      rcases hrow with h|h
      · have hg : g=(1+d)*(1/5) := by linear_combination -(1/5:K)*h
        rw [hg]
        have he : 1-(1+d)*(1/5)=(4-d)*(1/5) := by ring
        rw [he]
        simp [clockCandidates]
      · have hg : g=(2-d)*(1/3) := by linear_combination (1/3:K)*h
        rw [hg]
        have he : 1-(2-d)*(1/3)=(1+d)*(1/3) := by ring
        rw [he]
        simp [clockCandidates]

/-- The reflected quadratic primitive minus literal diagonal value. -/
def quadGate {K : Type*} [Field K] (d z e g : K) : K :=
  (1-z*z*z)*(1/3)-(d+e)*(1-z*z)*(1/2)+d*e*(1-z)-g*(z-d)*(z-e)

private theorem line_binding {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (d z : K) : value d z lineExpr = lineGate d z := by
  simp [lineExpr, lineGate, value]

private theorem candidate_binding {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (d z : K) :
    endChart.map (fun p => (value d z p.1,value d z p.2)) = clockCandidates d := by
  simp [endChart,clockCandidates,value]

private theorem quad_binding {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (d z : K) (p : Expr × Expr) :
    value d z (quadExpr p) = quadGate d z (value d z p.1) (value d z p.2) := by
  cases p
  simp [quadExpr, quadGate, value]

/-- Nonvanishing over every ordered field at any points enclosed by
two different fourth-Gauss brackets. -/
theorem line_checked {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {d z : K} {i j : Fin 4} (hd : encloses (rootBox i) d) (hz : encloses (rootBox j) z)
    (hij : i≠j) : lineGate d z ≠ 0 := by
  rw [← line_binding d z]
  exact checked hd hz hij (by simp [tests])

/-- All eight nonlinear chronology alternatives are excluded in each
of the twelve oriented fourth-Gauss box pairs. -/
theorem quad_checked {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {d z e g : K} {i j : Fin 4} (hd : encloses (rootBox i) d) (hz : encloses (rootBox j) z)
    (hij : i≠j) (hh : (e,g) ∈ clockCandidates d) : quadGate d z e g ≠ 0 := by
  rw [← candidate_binding d z] at hh
  obtain ⟨p,hp,he⟩ := List.mem_map.mp hh
  have hx : quadExpr p ∈ tests := List.mem_cons_of_mem _ (List.mem_map_of_mem hp)
  have hg := checked hd hz hij hx
  have he1 := congrArg Prod.fst he
  have he2 := congrArg Prod.snd he
  change value d z p.1 = e at he1
  change value d z p.2 = g at he2
  rw [quad_binding,he1,he2] at hg
  exact hg

/-- Independent check that the named brackets are for the shifted
fourth Legendre nodes, not just arbitrary intervals. -/
theorem brackets_check (i : Fin 4) :
    RKCert.ReviewedNative.SDIRK8TwoZeroLineScalarReceipt.quartic70 (rootBox i).lo *
      RKCert.ReviewedNative.SDIRK8TwoZeroLineScalarReceipt.quartic70 (rootBox i).hi < 0 :=
  rootBox_opposite_signs i

end RKCert.ReviewedNative.SDIRK8ThreeZeroSilentScalarReceipt
