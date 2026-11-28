module

public import RKCert.ReviewedNative.DIRK12MidpointForwardFlags
public import RKCert.ReviewedNative.DIRK12MidpointNormalizedScalar
public import RKCert.ReviewedNative.DIRK12MidpointRealWeightGuards
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Tactic.FieldSimp

@[expose] public section

/-! Actual real support clocks and literal physical weights in the causal
construction. The first live row and the fixed-coefficient mode relation
are wired literally. The remaining live-to-live entries are still open. -/
namespace RKResearch.Certified.DIRK12MidpointForward

open RKResearch Graded DualSupport12VectorReplay DIRK12MidpointGhost
open DIRK12MidpointRealInterval DirectedRatBox
open scoped Matrix BigOperators FiniteRootedTree

def leg5 (x : ℝ) : ℝ := 30+x*(-420+x*(1680+x*(-2520+x*1260)))
def leg6 (x : ℝ) : ℝ := -42+x*(840+x*(-5040+x*(12600+x*(-13860+x*5544))))
def leg7 (x : ℝ) : ℝ :=
  56+x*(-1512+x*(12600+x*(-46200+x*(83160+x*(-72072+x*24024)))))

noncomputable def gammaFrom (alpha : ℝ) : ℝ := (30*alpha-8)/35

theorem leg5_half : leg5 (1/2)=15/4 := by norm_num [leg5]
theorem leg6_half : leg6 (1/2)=0 := by norm_num [leg6]
theorem leg7_half : leg7 (1/2)=(-35)/8 := by norm_num [leg7]

/-- This is the literal first-live-row normalization of the existing
mode system, not an additional condition on the true constructor. -/
theorem mode_normalization (alpha mu : ℝ) :
    alpha*leg5 (1/2)+mu*leg6 (1/2)+gammaFrom alpha*leg7 (1/2)=1 := by
  rw [leg5_half,leg6_half,leg7_half,gammaFrom]
  ring

noncomputable def realClock (x f : ℝ) (i : Fin 10) : ℝ :=
  1-site x f (stageTag (visible i))

@[simp] theorem realClock_first (x f : ℝ) : realClock x f 0=1/2 := by
  change (1:ℝ)-((1/2:ℚ):ℝ)=1/2
  norm_num

noncomputable def realFeed (x f alpha mu nu : ℝ) (L : Fin 10 → Fin 10 → ℝ) : Feed ℝ where
  a := 1/2
  cVisible := realClock x f
  b := physicalWeight x f
  live i j := if i=0 then 0 else L i j
  mode0 i := (realClock x f i) *
    (alpha*leg5 (realClock x f i)+mu*leg6 (realClock x f i)+gammaFrom alpha*leg7 (realClock x f i))
  mode1 i := (realClock x f i)*nu*leg6 (realClock x f i)

section Actual

variable (x f alpha mu nu : ℝ) (L : Fin 10 → Fin 10 → ℝ)
local notation "thisFeed" => realFeed x f alpha mu nu L

theorem real_nodes (i : Fin 15) (hg : ¬ ghostRow i) :
    1 - nodes (thisFeed).tableau i = site x f (stageTag i) := by
  rw [(thisFeed).nodes_tableau]
  revert hg
  refine stage_cases (P:=fun i => ¬ ghostRow i → 1-(thisFeed).clocks i=site x f (stageTag i)) ?_ ?_ ?_ i
  · intro _
    change (1:ℝ)-0=1
    ring
  · intro g h
    exact (h (ghost_hidden g)).elim
  · intro j _
    rw [(thisFeed).clocks_visible]
    change 1 - (1-site x f (stageTag (visible j))) = _
    ring

theorem real_ghost_weights (g : Fin 4) : (thisFeed).b (hidden g)=0 := by
  change physicalWeight x f (hidden g)=0
  simp [physicalWeight]

theorem real_weight_guard (hx : Encloses xBox x) (hf : Encloses fBox f)
    (i : Fin 15) (hg : ¬ ghost i) : (thisFeed).b i ≠ 0 :=
  physicalWeight_nonzero hx hf i hg

theorem real_terminal_guard (hx : Encloses xBox x) (hf : Encloses fBox f) :
    (thisFeed).b terminal ≠ 0 :=
  real_weight_guard x f alpha mu nu L hx hf terminal (by decide)

theorem real_DIRK :
    Matrix.IsLowerTriangular (thisFeed).tableau ∧ (thisFeed).tableau 0 0=0 ∧
      (thisFeed).tableau (hidden 0) (hidden 0)≠0 := by
  apply (thisFeed).genuine_DIRK
  change (1/2:ℝ) ≠ 0
  norm_num

theorem literal_second_diag : (thisFeed).tableau (hidden 0) (hidden 0)=1/16 := by
  rw [Feed.tableau_hidden_hidden,DIRK12MidpointGhost.first_diagonal]
  change (1/2:ℝ)*((1/8:ℚ):ℝ)=1/16
  norm_num

theorem literal_terminal_clock : (thisFeed).clocks terminal=1 := by
  rw [← visible_terminal,Feed.clocks_visible]
  change (1:ℝ)-0=1
  ring

theorem literal_terminal_diag : (thisFeed).tableau terminal terminal=0 := by
  have e (i : Fin 14) : i.castSucc < terminal := by
    change i.val<14
    exact i.isLt
  change (thisFeed).corrected terminal (Fin.last 13)=0
  rw [Feed.corrected,ite_eq_left rfl,show (Fin.last 13).succ = terminal by decide,
    literal_terminal_clock x f alpha mu nu L]
  have cols (i : Fin 14) : (thisFeed).causal i.castSucc (Fin.last 13)=0 := by
    rw [Feed.causal,ite_eq_left (show i.castSucc < (Fin.last 13).succ by
      rw [show (Fin.last 13).succ=terminal by decide]
      exact e i)]
  have sum0 : (∑ i : Fin 14, (thisFeed).b i.castSucc*(thisFeed).causal i.castSucc (Fin.last 13))=0 :=
    Finset.sum_eq_zero (fun i _ => by rw [cols i,mul_zero])
  rw [sum0]
  simp

theorem real_scalar (hx : Encloses xBox x) (hf : Encloses fBox f)
    (hx0 : realX x=0) (hf0 : realF x f=0) :
    ∀ j < 12, ((j+1:Nat):ℝ)*row (thisFeed).b ((thisFeed).clocks^j)=1 := by
  rw [← (thisFeed).nodes_tableau]
  exact ordinary_scalar_with_physical_weights hx hf hx0 hf0 (thisFeed).tableau
    (real_nodes x f alpha mu nu L)

theorem real_adjoint (hx : Encloses xBox x) (hf : Encloses fBox f)
    (hx0 : realX x=0) (hf0 : realF x f=0) :
    mat (thisFeed).tableau.transpose (thisFeed).b=(thisFeed).b*(1-(thisFeed).clocks) := by
  apply (thisFeed).paid_adjoint (real_terminal_guard x f alpha mu nu L hx hf)
  · simpa using real_scalar x f alpha mu nu L hx hf hx0 hf0 0 (by decide)
  · simpa using real_scalar x f alpha mu nu L hx hf hx0 hf0 1 (by decide)

theorem real_star (hx : Encloses xBox x) (hf : Encloses fBox f)
    (hx0 : realX x=0) (hf0 : realF x f=0) :
    (starLo:ℝ) < (((FiniteRootedTree.bushyTree 13).factorial:Nat):ℝ)*
        ((thisFeed).b ⬝ᵥ Φ (FiniteRootedTree.bushyTree 13) (thisFeed).tableau)-1 ∧
    (((FiniteRootedTree.bushyTree 13).factorial:Nat):ℝ)*
        ((thisFeed).b ⬝ᵥ Φ (FiniteRootedTree.bushyTree 13) (thisFeed).tableau)-1 < (starHi:ℝ) :=
  (scalar_and_star_with_physical_weights hx hf hx0 hf0 (thisFeed).tableau
     (real_nodes x f alpha mu nu L)).2

theorem real_not_order13 (hx : Encloses xBox x) (hf : Encloses fBox f)
    (hx0 : realX x=0) (hf0 : realF x f=0) :
    ¬ HasOrder 13 (thisFeed).tableau (thisFeed).b := by
  intro assumed
  have e := assumed (FiniteRootedTree.bushyTree 13) (by decide +kernel)
  have h := (real_star x f alpha mu nu L hx hf hx0 hf0).1
  rw [e,sub_self] at h
  exact (not_lt_of_ge (by norm_num [starLo])) h

theorem first_live_budget (m : Fin 4) :
    ((m.val+2:Nat):ℝ) * (∑ j, (if (0:Fin 10)<j then 0 else (thisFeed).live 0 j) * (thisFeed).cVisible j^(m.val+1)) +
      (thisFeed).mode0 0*(thisFeed).a^(m.val+1) +
      (((m.val+2:Nat):ℝ)/((m.val+3:Nat):ℝ))*(thisFeed).mode1 0*(thisFeed).a^(m.val+2) =
      (thisFeed).cVisible 0^(m.val+2) := by
  have e : (thisFeed).mode0 0 = (1/2:ℝ) := by
    change realClock x f 0 *
      (alpha*leg5 (realClock x f 0)+mu*leg6 (realClock x f 0)+
      gammaFrom alpha*leg7 (realClock x f 0)) = _
    rw [realClock_first,mode_normalization,mul_one]
  have e' : (thisFeed).mode1 0 = 0 := by
    change realClock x f 0*nu*leg6 (realClock x f 0)=_
    rw [realClock_first,leg6_half,mul_zero]
  have c : (thisFeed).cVisible 0 = (1/2:ℝ) := realClock_first _ _
  rw [e,e',c]
  simp [realFeed,pow_succ,mul_comm]

/-- The first live row is primitive-exact for all four paid nonzero powers,
independently of every later row and without assuming any live budget. -/
theorem first_live_primitive (m : Fin 4) :
    DualSupport12.forward (thisFeed).tableau (m.val+1) (visible 0) = 0 := by
  have ne : visible (0:Fin 10) ≠ terminal := by decide
  have mode0 : (thisFeed).mode0 0=(1/2:ℝ) := by
    change realClock x f 0 *
      (alpha*leg5 (realClock x f 0)+mu*leg6 (realClock x f 0)+
      gammaFrom alpha*leg7 (realClock x f 0)) = _
    rw [realClock_first,mode_normalization,mul_one]
  have mode1 : (thisFeed).mode1 0=0 := by
    change realClock x f 0*nu*leg6 (realClock x f 0)=_
    rw [realClock_first,leg6_half,mul_zero]
  have hmoment :
      (∑ g : Fin 4, (tap g : ℝ)*(clock g : ℝ)^(m.val+1)) =
      1/((m.val+2:Nat):ℝ) := by
    have e := congrArg (fun q : Rat => (q : ℝ)) (moments (⟨m.val,by omega⟩ : Fin 5))
    simpa [add4,add_assoc,Fin.sum_univ_succ,Rat.cast_div] using e
  have hentry (j : Fin 10) : (thisFeed).tableau (visible 0) (visible j)=0 := by
    rw [(thisFeed).tableau_nonterminal_live (0 : Fin 10) j ne]
    simp [realFeed]
  rw [DualSupport12.forward,(thisFeed).nodes_tableau]
  simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.pow_apply]
  change ((m.val+1+1:Nat):ℝ) *
      (∑ j, (thisFeed).tableau (visible 0) j * (thisFeed).clocks j^(m.val+1)) -
      (thisFeed).clocks (visible 0)^(m.val+1+1) = 0
  rw [sum_stages]
  simp only [Feed.clocks_origin,zero_pow (by omega : m.val+1≠0),mul_zero,zero_add,
    hentry,zero_mul,Finset.sum_const_zero,add_zero,
    (thisFeed).tableau_nonterminal_tap _ _ ne,Feed.ghostTap,mode0,mode1,
    Feed.clocks_hidden,Feed.clocks_visible,mul_pow]
  have ap : (thisFeed).a=(1/2:ℝ) := rfl
  have cp : (thisFeed).cVisible 0=(1/2:ℝ) := realClock_first _ _
  rw [ap,cp,show m.val+1+1=m.val+2 by omega]
  have eq :
      (∑ g : Fin 4,
        (tap g:ℝ)*((1/2:ℝ)+0*((1/2:ℝ)*(clock g:ℝ)))*
          ((1/2:ℝ)^(m.val+1)*(clock g:ℝ)^(m.val+1))) =
      (1/2:ℝ)^(m.val+2)*∑ g : Fin 4, (tap g:ℝ)*(clock g:ℝ)^(m.val+1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [show m.val+2=m.val+1+1 by omega,pow_succ]
    ring
  simp only [zero_mul,add_zero] at eq
  rw [eq,hmoment]
  field_simp [Nat.cast_ne_zero.mpr (show m.val+2≠0 by omega)]
  ring

/-- Only 32 physical nonterminal live primitive reads remain, after the
first live row (four entering powers) is paid literally. -/
def RealLiveRemainder : Prop :=
  ∀ (m : Fin 4) (i : Fin 10), i ≠ 0 → visible i ≠ terminal →
    ((m.val+2:Nat):ℝ) * (∑ j, (if i<j then 0 else (thisFeed).live i j) * (thisFeed).cVisible j^(m.val+1)) +
      (thisFeed).mode0 i*(thisFeed).a^(m.val+1) +
      (((m.val+2:Nat):ℝ)/((m.val+3:Nat):ℝ))*(thisFeed).mode1 i*(thisFeed).a^(m.val+2) =
      (thisFeed).cVisible i^(m.val+2)

theorem real_live_budget (rest : RealLiveRemainder x f alpha mu nu L) : (thisFeed).LiveBudget := by
  intro m i hn
  by_cases z : i=0
  · subst i
    exact first_live_budget x f alpha mu nu L m
  · exact rest m i z hn

theorem real_fw_A (hx : Encloses xBox x) (hf : Encloses fBox f)
    (hx0 : realX x=0) (hf0 : realF x f=0) (j : Nat) (hj : j<5) :
    ∀ v ∈ forwardBand ℝ j, mat (thisFeed).tableau v ∈ forwardBand ℝ (j+1) :=
  (thisFeed).fw_A (real_terminal_guard x f alpha mu nu L hx hf) (real_ghost_weights x f alpha mu nu L)
    (real_adjoint x f alpha mu nu L hx hf hx0 hf0) j hj

theorem real_fw_primitive (hx : Encloses xBox x) (hf : Encloses fBox f)
    (hx0 : realX x=0) (hf0 : realF x f=0)
    (rest : RealLiveRemainder x f alpha mu nu L) (j : Nat) (hj : j<5) :
    DualSupport12.forward (thisFeed).tableau j ∈ forwardBand ℝ (j+1) :=
  (thisFeed).fw_primitive (real_terminal_guard x f alpha mu nu L hx hf)
    (real_ghost_weights x f alpha mu nu L) (real_adjoint x f alpha mu nu L hx hf hx0 hf0)
    (real_scalar x f alpha mu nu L hx hf hx0 hf0) (real_live_budget x f alpha mu nu L rest) j hj

end Actual
end RKResearch.Certified.DIRK12MidpointForward

#print axioms RKResearch.Certified.DIRK12MidpointForward.real_nodes
#print axioms RKResearch.Certified.DIRK12MidpointForward.real_adjoint
#print axioms RKResearch.Certified.DIRK12MidpointForward.real_star
#print axioms RKResearch.Certified.DIRK12MidpointForward.real_not_order13
#print axioms RKResearch.Certified.DIRK12MidpointForward.first_live_budget
#print axioms RKResearch.Certified.DIRK12MidpointForward.first_live_primitive
#print axioms RKResearch.Certified.DIRK12MidpointForward.literal_terminal_diag
#print axioms RKResearch.Certified.DIRK12MidpointForward.real_fw_primitive
