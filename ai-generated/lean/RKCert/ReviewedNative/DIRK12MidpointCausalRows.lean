module

public import RKCert.ReviewedNative.DualSupport12VectorReplay
public import RKCert.ReviewedNative.DIRKOrderTwelveMidpointGhostForwardCore
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

@[expose] public section

/-! The causal assembly of the midpoint construction, with an open literal
live-to-live block. The prescribed row sums and actual reflected first
adjoint are identities of this physical matrix, not scalar proxies. -/
namespace RKResearch.Certified.DIRK12MidpointForward

open RKResearch Graded DualSupport12VectorReplay
open scoped Matrix BigOperators

abbrev V15 (K : Type*) := Fin 15 → K
abbrev H := RKResearch.Certified.DIRK12MidpointGhost.clock

def hidden (i : Fin 4) : Fin 15 := (Fin.castAdd 10 i).succ
def visible (i : Fin 10) : Fin 15 := (Fin.natAdd 4 i).succ
abbrev terminal : Fin 15 := Fin.last 14

@[simp] theorem hidden_val (i : Fin 4) : (hidden i).val = i.val+1 := rfl
@[simp] theorem visible_val (i : Fin 10) : (visible i).val = 5+i.val := by
  change 4+i.val+1=5+i.val
  omega

@[simp] theorem hidden_nonzero (i : Fin 4) : hidden i ≠ 0 := by
  intro h
  have q := congrArg Fin.val h
  simp at q

@[simp] theorem hidden_not_terminal (i : Fin 4) : hidden i ≠ terminal := by
  intro h
  have q := congrArg Fin.val h
  simp only [hidden_val, Fin.val_last] at q
  omega

@[simp] theorem visible_nonzero (i : Fin 10) : visible i ≠ 0 := by
  intro h
  have q := congrArg Fin.val h
  simp at q

@[simp] theorem ghost_hidden (i : Fin 4) : ghost (hidden i) := by
  change 1 ≤ (hidden i).val ∧ (hidden i).val ≤ 4
  simp only [hidden_val]
  omega

@[simp] theorem non_ghost_visible (i : Fin 10) : ¬ ghost (visible i) := by
  change ¬ (1 ≤ (visible i).val ∧ (visible i).val ≤ 4)
  simp only [visible_val]
  omega

@[simp] theorem non_ghost_origin : ¬ ghost (0 : Fin 15) := by decide

theorem stage_cases {P : Fin 15 → Prop} (z : P 0)
    (h : ∀ g, P (hidden g)) (v : ∀ j, P (visible j)) (i : Fin 15) : P i := by
  refine Fin.cases z (fun j => ?_) i
  exact Fin.addCases (m := 4) (n := 10) h v j

@[simp] theorem visible_terminal : visible (Fin.last 9) = terminal := by decide

theorem sum_stages {K : Type*} [AddCommMonoid K] (w : V15 K) :
    (∑ i, w i) = w 0 + ((∑ g, w (hidden g)) + ∑ j, w (visible j)) := by
  rw [Fin.sum_univ_succ]
  exact congrArg (w 0 + ·) (Fin.sum_univ_add (fun i : Fin (4+10) => w i.succ))

variable {K : Type*} [Field K] [CharZero K]

structure Feed (K : Type*) where
  a : K
  cVisible : Fin 10 → K
  b : V15 K
  live : Fin 10 → Fin 10 → K
  mode0 : Fin 10 → K
  mode1 : Fin 10 → K

namespace Feed

variable (P : Feed K)

set_option linter.unusedSectionVars false
open DIRK12MidpointGhost

/-- The hidden origin column is not stored: it fills the actual row sums. -/
def clocks (i : Fin 15) : K :=
  Fin.cases (motive:=fun _ => K) 0
    (fun r => Fin.addCases (motive:=fun _ => K)
      (fun g : Fin 4 => P.a * (clock g : K)) P.cVisible r) i

@[simp] theorem clocks_origin : P.clocks 0 = 0 := rfl
@[simp] theorem clocks_hidden (g : Fin 4) : P.clocks (hidden g) = P.a*(clock g : K) := by
  simp [clocks,hidden]
@[simp] theorem clocks_visible (j : Fin 10) : P.clocks (visible j) = P.cVisible j := by
  simp [clocks,visible]

def ghostTap (j : Fin 10) (g : Fin 4) : K :=
  (tap g : K) * (P.mode0 j + P.mode1 j * P.clocks (hidden g))

/-- Before triangular truncation or the terminal column correction. -/
def seed (i : Fin 15) (j : Fin 14) : K :=
  Fin.cases (motive:=fun _ => K) 0 (fun r =>
    Fin.addCases (motive:=fun _ => K)
      (fun g => Fin.addCases (motive:=fun _ => K)
        (fun h : Fin 4 => P.a*(block g h : K)) (fun _ : Fin 10 => 0) j)
      (fun s => Fin.addCases (motive:=fun _ => K) (P.ghostTap s) (P.live s) j) r) i

def causal (i : Fin 15) (j : Fin 14) : K :=
  if i < j.succ then 0 else P.seed i j

@[simp] theorem causal_origin (j : Fin 14) : P.causal 0 j = 0 := by
  simp [causal]

@[simp] theorem causal_hidden_hidden (g h : Fin 4) :
    P.causal (hidden g) (Fin.castAdd 10 h) = P.a*(block g h : K) := by
  by_cases e : hidden g < hidden h
  · have e' : g < h := by
      change (hidden g).val < (hidden h).val at e
      simpa using e
    rw [causal, ite_eq_left (show hidden g < (Fin.castAdd 10 h).succ from e)]
    simp [triangular _ _ e']
  · rw [causal, ite_eq_right (show ¬ hidden g < (Fin.castAdd 10 h).succ from e)]
    simp [seed,hidden]

@[simp] theorem causal_hidden_visible (g : Fin 4) (j : Fin 10) :
    P.causal (hidden g) (Fin.natAdd 4 j) = 0 := by
  have e : hidden g < visible j := by
    change (hidden g).val < (visible j).val
    simp only [hidden_val,visible_val]
    omega
  exact ite_eq_left (show hidden g < (Fin.natAdd 4 j).succ from e)

@[simp] theorem causal_visible_hidden (j : Fin 10) (g : Fin 4) :
    P.causal (visible j) (Fin.castAdd 10 g) = P.ghostTap j g := by
  have e : ¬ visible j < hidden g := by
    change ¬ (visible j).val < (hidden g).val
    simp only [hidden_val,visible_val]
    omega
  rw [causal,ite_eq_right (show ¬ visible j < (Fin.castAdd 10 g).succ from e)]
  simp [seed,visible]

theorem causal_visible_visible (i j : Fin 10) :
    P.causal (visible i) (Fin.natAdd 4 j) =
      if i < j then 0 else P.live i j := by
  have g : visible i < (Fin.natAdd 4 j).succ ↔ i<j := by
    change 4+i.val+1<4+j.val+1 ↔ i.val<j.val
    omega
  rw [causal]
  by_cases h : i<j
  · rw [ite_eq_left (g.mpr h),ite_eq_left h]
  · rw [ite_eq_right (mt g.mp h),ite_eq_right h]
    simp [seed,visible]

/-- Correct a physical terminal column by the desired weighted adjoint.
Only the terminal weight occurs in a denominator. -/
def corrected (i : Fin 15) (j : Fin 14) : K :=
  if i = terminal then
    (P.b j.succ * (1-P.clocks j.succ) -
      ∑ r : Fin 14, P.b r.castSucc * P.causal r.castSucc j) / P.b terminal
  else P.causal i j

def tableau : Matrix (Fin 15) (Fin 15) K := fun i j =>
  Fin.cases (motive:=fun _ => K) (P.clocks i - ∑ k : Fin 14, P.corrected i k) (P.corrected i) j

@[simp] theorem tableau_succ (i : Fin 15) (j : Fin 14) :
    P.tableau i j.succ = P.corrected i j := rfl

theorem nodes_tableau : nodes P.tableau = P.clocks := by
  ext i
  change (∑ j : Fin 15, P.tableau i j * (1 : K)) = _
  rw [Fin.sum_univ_succ]
  simp [tableau]

theorem isLower : Matrix.IsLowerTriangular P.tableau := by
  intro i j hij
  change i < j at hij
  refine Fin.cases ?_ (fun r => ?_) j hij
  · intro h
    omega
  · intro h
    have nt : i ≠ terminal := by
      intro e
      subst i
      change 14 < r.val+1 at h
      omega
    simp [corrected,causal,h,nt]

theorem tableau_zero_diag : P.tableau 0 0 = 0 := by
  have e : (0 : Fin 15) ≠ terminal := by decide
  simp [tableau,corrected,e]

theorem tableau_origin (j : Fin 15) : P.tableau 0 j = 0 := by
  refine Fin.cases P.tableau_zero_diag (fun r => ?_) j
  rw [tableau_succ,corrected,ite_eq_right (by decide : (0:Fin 15) ≠ terminal)]
  simp

@[simp] theorem tableau_hidden_hidden (g h : Fin 4) :
    P.tableau (hidden g) (hidden h) = P.a * (block g h : K) := by
  change P.corrected (hidden g) (Fin.castAdd 10 h) = _
  rw [corrected,ite_eq_right (hidden_not_terminal g)]
  simp

@[simp] theorem tableau_hidden_visible (g : Fin 4) (j : Fin 10) :
    P.tableau (hidden g) (visible j) = 0 := by
  change P.corrected (hidden g) (Fin.natAdd 4 j) = 0
  rw [corrected,ite_eq_right (hidden_not_terminal g)]
  simp

theorem tableau_nonterminal_tap (j : Fin 10) (g : Fin 4)
    (hn : visible j ≠ terminal) :
    P.tableau (visible j) (hidden g) = P.ghostTap j g := by
  change P.corrected (visible j) (Fin.castAdd 10 g) = _
  rw [corrected,ite_eq_right hn]
  simp

theorem tableau_nonterminal_live (i j : Fin 10) (hn : visible i ≠ terminal) :
    P.tableau (visible i) (visible j) =
      if i<j then 0 else P.live i j := by
  change P.corrected (visible i) (Fin.natAdd 4 j) = _
  rw [corrected,ite_eq_right hn]
  apply causal_visible_visible

theorem genuine_DIRK (a0 : P.a ≠ 0) :
    Matrix.IsLowerTriangular P.tableau ∧ P.tableau 0 0 = 0 ∧
      P.tableau (hidden 0) (hidden 0) ≠ 0 := by
  refine ⟨P.isLower,P.tableau_zero_diag,?_⟩
  rw [tableau_hidden_hidden,first_diagonal]
  exact mul_ne_zero a0 (by norm_num)

theorem paid_adjoint_column (h : P.b terminal ≠ 0) (j : Fin 14) :
    mat P.tableau.transpose P.b j.succ = P.b j.succ * (1-P.clocks j.succ) := by
  change (∑ r : Fin 15, P.tableau r j.succ * P.b r) = _
  rw [Fin.sum_univ_castSucc]
  have e (r : Fin 14) : r.castSucc ≠ terminal := by
    intro q
    have e := congrArg Fin.val q
    simp only [Fin.val_castSucc,Fin.val_last] at e
    omega
  simp only [tableau_succ,corrected,e,ite_false,ite_true,div_mul_cancel₀ _ h]
  rw [show (∑ r : Fin 14, P.causal r.castSucc j * P.b r.castSucc) =
      ∑ r : Fin 14, P.b r.castSucc * P.causal r.castSucc j from by
      apply Finset.sum_congr rfl
      intro r _
      exact mul_comm _ _]
  ring

/-- The origin is included in D(1) by the two already paid scalar moments.
All actual non-origin columns satisfy D(1) entry by entry. -/
theorem paid_adjoint (h : P.b terminal ≠ 0)
    (scalar0 : row P.b (1 : V15 K) = 1)
    (scalar1 : 2 * row P.b P.clocks = 1) :
    mat P.tableau.transpose P.b = P.b * (1-P.clocks) := by
  have e : row (mat P.tableau.transpose P.b) (1 : V15 K) = row P.b P.clocks := by
    rw [row_apply,mat_apply,dotProduct_comm,Matrix.dotProduct_transpose_mulVec]
    change row P.b (nodes P.tableau) = _
    rw [nodes_tableau]
  have e' : row (P.b * (1-P.clocks)) (1 : V15 K) = row P.b P.clocks := by
    have eq : row (P.b * (1-P.clocks)) (1 : V15 K) =
        row P.b (1-P.clocks) := by
      simp only [row_apply,dotProduct,Pi.mul_apply,Pi.one_apply,mul_one]
    rw [eq,map_sub,scalar0]
    linear_combination -scalar1
  rw [row_apply,row_apply,dotProduct,dotProduct] at e e'
  simp only [Pi.one_apply,mul_one,Pi.mul_apply,Pi.sub_apply] at e'
  simp only [Pi.one_apply,mul_one] at e
  conv at e => lhs; rw [Fin.sum_univ_succ]
  conv at e' => lhs; rw [Fin.sum_univ_succ]
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · have tail : (∑ j : Fin 14, mat P.tableau.transpose P.b j.succ) =
        ∑ j : Fin 14, P.b j.succ * (1-P.clocks j.succ) := by
      apply Finset.sum_congr rfl
      intro j _
      exact P.paid_adjoint_column h j
    rw [tail] at e
    change mat P.tableau.transpose P.b 0 = P.b 0 * (1-P.clocks 0)
    linear_combination e-e'
  · exact P.paid_adjoint_column h j

end Feed

end RKResearch.Certified.DIRK12MidpointForward

#print axioms RKResearch.Certified.DIRK12MidpointForward.Feed.nodes_tableau
#print axioms RKResearch.Certified.DIRK12MidpointForward.Feed.genuine_DIRK
#print axioms RKResearch.Certified.DIRK12MidpointForward.Feed.paid_adjoint
