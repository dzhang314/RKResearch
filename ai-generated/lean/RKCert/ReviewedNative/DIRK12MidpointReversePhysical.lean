module

public import RKCert.ReviewedNative.DIRK12MidpointReverseGroups
public import RKCert.ReviewedNative.DIRK12MidpointCausalRows
public import RKCert.ReviewedNative.DIRK12MidpointLateCompletion
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! A physical width-fifteen extension of a given five-row ordinary
head. Nothing is replaced in that head. The four new ordinary rows
implement the literal grouped-return and three seed prescriptions;
the given Feed supplies the actual ghost, origin and terminal columns. -/
namespace RKResearch.Certified.DIRK12MidpointReverse.Physical

open RKResearch Graded
open DIRK12MidpointForward DIRK12MidpointForward.Late
open scoped BigOperators Matrix

set_option linter.unusedSectionVars false

def head (i : Fin 5) : Fin 10 := Fin.castAdd 5 i
def earlyTarget (i : Fin 6) : Fin 10 := Fin.castAdd 4 i
def lateTarget (i : Fin 4) : Fin 10 := Fin.natAdd 6 i
def returnRow (i : Fin 4) : Fin 10 := Fin.natAdd 5 (Fin.castAdd 1 i)
def seedTarget (i : Fin 3) : Fin 10 := lateTarget (Fin.castAdd 1 i)

@[simp] theorem head_val (i : Fin 5) : (head i).val=i.val := rfl
@[simp] theorem earlyTarget_val (i : Fin 6) : (earlyTarget i).val=i.val := rfl
@[simp] theorem lateTarget_val (i : Fin 4) : (lateTarget i).val=6+i.val := rfl
@[simp] theorem returnRow_val (i : Fin 4) : (returnRow i).val=5+i.val := rfl
@[simp] theorem seedTarget_val (i : Fin 3) : (seedTarget i).val=6+i.val := rfl
@[simp] theorem lateTarget_last : lateTarget 3=9 := by decide
@[simp] theorem return_seed (i : Fin 3) : returnRow i.succ=seedTarget i := by
  apply Fin.ext
  simp
  omega
@[simp] theorem seed_target0 : seedTarget 0=6 := by decide
@[simp] theorem seed_target1 : seedTarget 1=7 := by decide
@[simp] theorem seed_target2 : seedTarget 2=8 := by decide
@[simp] theorem return_row0 : returnRow 0=5 := by decide
@[simp] theorem return_row1 : returnRow 1=6 := by decide
@[simp] theorem return_row2 : returnRow 2=7 := by decide
@[simp] theorem return_row3 : returnRow 3=8 := by decide
@[simp] theorem physical_return0 : visible (returnRow 0)=10 := by decide
@[simp] theorem physical_return1 : visible (returnRow 1)=11 := by decide
@[simp] theorem physical_return2 : visible (returnRow 2)=12 := by decide
@[simp] theorem physical_return3 : visible (returnRow 3)=13 := by decide
@[simp] theorem physical_term : visible (9:Fin 10)=terminal := by decide

private theorem head_nt (i : Fin 5) : visible (head i) ≠ terminal := by
  intro e
  have h := congrArg Fin.val e
  simp only [visible_val,head_val,Fin.val_last] at h
  omega

private theorem ret_nt (i : Fin 4) : visible (returnRow i) ≠ terminal := by
  intro e
  have h := congrArg Fin.val e
  simp only [visible_val,returnRow_val,Fin.val_last] at h
  omega

private theorem ret_ge (s : Fin 4) (i : Fin 6) : ¬ returnRow s < earlyTarget i := by
  change ¬ (5+s.val < i.val)
  omega

variable {K : Type*} [Field K] [CharZero K]

structure Data (K : Type*) where
  /-- Physical reflected clock of each repeated site. -/
  d : K
  /-- Normalized reflected clocks at the two other return sites. -/
  r : K
  t : K
  /-- Deweighted normalized barycentric profile on the grouped targets. -/
  h : Fin 6 → K

variable (P : Feed K) (D : Data K)

/-- The geometric facts needed for this exact transfer. They do not
assert any reverse primitive or a bridge property. -/
structure Geom : Prop where
  d0 : D.d ≠ 0
  r0 : D.r ≠ 0
  r1 : D.r ≠ 1
  r2 : D.r ≠ 2
  t0 : D.t ≠ 0
  t1 : D.t ≠ 1
  tr : D.t ≠ D.r
  bNZ : ∀ i : Fin 10, P.b (visible i) ≠ 0
  double : P.b 11=P.b 13
  ghost0 : ∀ g : Fin 4, P.b (hidden g)=0
  clockR : ∀ s : Fin 4, 1-P.clocks (visible (returnRow s)) =
    D.d * Groups.sourceClock D.r D.t s
  term1 : P.clocks terminal=1
  same0 : P.mode0 8=P.mode0 6
  same1 : P.mode1 8=P.mode1 6

/-- Reflected clocks in the normalized scale. -/
def Z (i : Fin 10) : K := (1-P.clocks (visible i))/D.d

/-- Existing causal head entries in deweighted target/source order. -/
def past (i : Fin 6) (j : Fin 5) : K :=
  (if head j < earlyTarget i then 0 else P.live (head j) (earlyTarget i))*
    P.b (visible (head j))/(D.d*P.b (visible (earlyTarget i)))

def pastRead (i : Fin 6) (m : Fin 3) : K :=
  ∑ j : Fin 5, past P D i j*(Z P D (head j))^(m.val+1)

noncomputable def grouped (i : Fin 6) (j : Fin 4) : K :=
  Groups.table D.r D.t (Z P D (earlyTarget i)) (D.h i) (pastRead P D i) j

/-- The normalized return entry in target,source order. The u row is
chronologically before all seed targets, and the terminal column of
the forward tableau has no physical nonterminal entry. -/
noncomputable def retEntry (i : Fin 10) (j : Fin 4) : K :=
  Fin.addCases (m:=6) (n:=4) (fun i => grouped P D i j)
    (fun k => Fin.addCases (m:=3) (n:=1)
      (fun t => Fin.cases 0 (fun s => Seed.table D.r t s) j) (fun _ => 0) k) i

@[simp] theorem retEntry_early (i : Fin 6) (j : Fin 4) :
    retEntry P D (earlyTarget i) j=grouped P D i j := by
  simp [retEntry,earlyTarget]

@[simp] theorem retEntry_seed0 (i : Fin 3) :
    retEntry P D (seedTarget i) 0=0 := by
  simp [retEntry,seedTarget,lateTarget,Fin.addCases_right]

@[simp] theorem retEntry_seed (i j : Fin 3) :
    retEntry P D (seedTarget i) j.succ=Seed.table D.r i j := by
  simp [retEntry,seedTarget,lateTarget,Fin.addCases_right]

@[simp] theorem retEntry_end (j : Fin 4) : retEntry P D 9 j=0 := by
  unfold retEntry
  rw [show (9:Fin 10)=Fin.natAdd 6 (Fin.natAdd 3 (0:Fin 1)) by decide,
    Fin.addCases_right,Fin.addCases_right]

theorem ret_causal (i : Fin 10) (j : Fin 4) (h : returnRow j < i) : retEntry P D i j=0 := by
  refine Fin.addCases (m:=6) (n:=4) (motive:=fun i =>
    returnRow j < i → retEntry P D i j=0) (fun k h => ?_) (fun k => ?_) i h
  · exact (ret_ge j k h).elim
  · refine Fin.addCases (m:=3) (n:=1) (motive:=fun k =>
      returnRow j < lateTarget k → retEntry P D (lateTarget k) j=0)
        (fun k => ?_) (fun z => ?_) k
    · change returnRow j < seedTarget k → retEntry P D (seedTarget k) j=0
      refine Fin.cases (motive:=fun j =>
        returnRow j < seedTarget k → retEntry P D (seedTarget k) j=0)
          (fun _ => retEntry_seed0 P D k) (fun l e => ?_) j
      rw [retEntry_seed,Seed.causal]
      rw [return_seed] at e
      change 6+l.val < 6+k.val at e
      change l.val < k.val
      omega
    · have e : Fin.natAdd 3 z=(3:Fin 4) := by
        have q := z.isLt
        apply Fin.ext
        change 3+z.val=3
        omega
      rw [e,lateTarget_last,retEntry_end]
      intro
      rfl

noncomputable def live (s i : Fin 10) : K :=
  Fin.addCases (m:=5) (n:=5) (fun j => P.live (head j) i)
    (fun r => Fin.addCases (m:=4) (n:=1) (fun j =>
      D.d*retEntry P D i j*P.b (visible i)/P.b (visible (returnRow j)))
      (fun _ => 0) r) s

noncomputable def feed : Feed K := { P with live := live P D }

@[simp] theorem feed_clocks : (feed P D).clocks=P.clocks := rfl
@[simp] theorem feed_b : (feed P D).b=P.b := rfl

local notation "Aphys" => (Feed.tableau (feed P D))

@[simp] theorem nodes_eq : nodes Aphys=P.clocks := (feed P D).nodes_tableau

theorem head_entry (s : Fin 5) (i : Fin 10) :
    Aphys (visible (head s)) (visible i) =
      if head s < i then 0 else P.live (head s) i := by
  rw [(feed P D).tableau_nonterminal_live (head s) i (head_nt s)]
  by_cases h : head s < i
  · rw [ite_eq_left h,ite_eq_left h]
  · rw [ite_eq_right h,ite_eq_right h]
    change live P D (Fin.castAdd 5 s) i=P.live (head s) i
    unfold live
    rw [Fin.addCases_left]

theorem return_entry (j : Fin 4) (i : Fin 10) :
    Aphys (visible (returnRow j)) (visible i) =
      D.d*retEntry P D i j*P.b (visible i)/P.b (visible (returnRow j)) := by
  rw [(feed P D).tableau_nonterminal_live (returnRow j) i (ret_nt j)]
  by_cases h : returnRow j < i
  · simp [h,ret_causal P D i j h]
  · rw [ite_eq_right h]
    change live P D (Fin.natAdd 5 (Fin.castAdd 1 j)) i=_
    unfold live
    rw [Fin.addCases_right,Fin.addCases_left]

theorem terminal_column (g : Geom P D) (i : Fin 15) :
    Aphys i terminal=0 := by
  by_cases e : i=terminal
  · subst i
    have Q : (∑ r : Fin 14, P.b r.castSucc*(feed P D).causal r.castSucc (Fin.last 13))=0 := by
      apply Finset.sum_eq_zero
      intro r _
      have le : r.castSucc < (Fin.last 13).succ := by
        change r.val < 14
        omega
      rw [Feed.causal,ite_eq_left le,mul_zero]
    change (feed P D).corrected terminal (Fin.last 13)=0
    rw [Feed.corrected,ite_eq_left rfl,show (Fin.last 13).succ=terminal by decide,
      feed_clocks, g.term1, feed_b, Q]
    simp
  · have le : i < terminal := lt_of_le_of_ne (Fin.le_last _) e
    exact (feed P D).isLower le

theorem normalized_return_clock (g : Geom P D) (j : Fin 4) :
    Z P D (returnRow j)=Groups.sourceClock D.r D.t j := by
  rw [Z,g.clockR]
  exact mul_div_cancel_left₀ _ g.d0

theorem same_seed_clocks (g : Geom P D) : nodes Aphys 11=nodes Aphys 13 := by
  have p := g.clockR 1
  have q := g.clockR 3
  simp [Groups.sourceClock] at p q
  rw [nodes_eq P D]
  change P.cVisible 6=P.cVisible 8
  linear_combination q-p

def paired : K := D.d^3*P.b 13*Seed.sigma

theorem paired_nz (g : Geom P D) : paired P D≠0 :=
  mul_ne_zero (mul_ne_zero (pow_ne_zero _ g.d0) (g.bNZ 8)) Seed.sigma_nz

def G : V15 K := physicalPair (paired P D)

/-- The reverse image profile is specified by the deweighted barycentric
data on the ten ordinary visible positions. The origin is fixed by
zero total sum; it is not inserted as a free reverse actuator. -/
def ampl (i : Fin 10) : K :=
  Fin.addCases (m:=6) (n:=4) D.h (Fin.addCases (m:=3) (n:=1)
    (Seed.bary D.r) (fun _ => 0)) i

@[simp] theorem ampl_early (i : Fin 6) : ampl D (earlyTarget i)=D.h i := by
  simp [ampl,earlyTarget]
@[simp] theorem ampl_seed (i : Fin 3) : ampl D (seedTarget i)=Seed.bary D.r i := by
  simp [ampl,seedTarget,lateTarget,Fin.addCases_right]
@[simp] theorem ampl_terminal : ampl D 9=0 := by
  unfold ampl
  rw [show (9:Fin 10)=Fin.natAdd 6 (Fin.natAdd 3 (0:Fin 1)) by decide,
    Fin.addCases_right,Fin.addCases_right]

def hv (i : Fin 10) : K := D.d^4*P.b (visible i)*ampl D i

def H (i : Fin 15) : K :=
  Fin.cases (motive:=fun _ => K) (-(∑ j : Fin 10, hv P D j))
    (Fin.addCases (m:=4) (n:=10) (fun _ => 0) (hv P D)) i

@[simp] theorem H_visible (i : Fin 10) : H P D (visible i)=hv P D i := by
  simp [H,visible,Fin.addCases_right]

@[simp] theorem H_hidden (i : Fin 4) : H P D (hidden i)=0 := by
  simp [H,DIRK12MidpointForward.hidden]

@[simp] theorem H_origin : H P D 0=-(∑ j : Fin 10, hv P D j) := rfl

@[simp] theorem H_sum : (∑ i : Fin 15, H P D i)=0 := by
  rw [sum_stages]
  simp

private theorem mat_pair (A : Matrix (Fin 15) (Fin 15) K) (s : K) (i : Fin 15) :
    mat A.transpose (physicalPair s) i=s*(A 13 i - A 11 i) := by
  have q := physicalPair_read s (fun j => A j i)
  simpa only [row_apply,mat_apply,Matrix.mulVec,Matrix.transpose_apply,dotProduct_comm]
    using q

theorem target_cases {Q : Fin 10 → Prop} (early : ∀ i, Q (earlyTarget i))
    (seed : ∀ i, Q (seedTarget i)) (term : Q 9) (i : Fin 10) : Q i := by
  refine Fin.addCases (m:=6) (n:=4) (motive:=Q) early
    (fun k => ?_) i
  refine Fin.addCases (m:=3) (n:=1) (motive:=fun k => Q (lateTarget k)) seed
    (fun z => ?_) k
  have e : (Fin.natAdd 3 z : Fin 4)=3 := by
    have q := z.isLt
    apply Fin.ext
    change 3+z.val=3
    omega
  rw [e,lateTarget_last]
  exact term

theorem pair_early (i : Fin 6) : physicalPair (paired P D) (visible (earlyTarget i))=0 := by
  have k : (visible (earlyTarget i)).val≤10 := by simp; omega
  unfold physicalPair
  rw [ite_eq_right,ite_eq_right]
  · intro e
    have q := congrArg Fin.val e
    change (visible (earlyTarget i)).val=11 at q
    omega
  · intro e
    have q := congrArg Fin.val e
    change (visible (earlyTarget i)).val=13 at q
    omega

theorem pair_seed (g : Geom P D) (i : Fin 3) :
    physicalPair (paired P D) (visible (seedTarget i)) =
        D.d^3*P.b (visible (seedTarget i))*Seed.pair i := by
  fin_cases i <;>
    norm_num [physicalPair,paired,Seed.pair,g.double,
      show visible (6:Fin 10)=11 by decide,show visible (7:Fin 10)=12 by decide,
      show visible (8:Fin 10)=13 by decide]

theorem actual_pair_visible (g : Geom P D) (i : Fin 10) :
    mat (Matrix.transpose Aphys) (G P D) (visible i)=((D.d/2) • G P D+H P D) (visible i) := by
  rw [G,mat_pair,←physical_return3,←physical_return1,return_entry,return_entry,
    physical_return3,physical_return1]
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,H_visible,hv]
  have b13 : P.b 13≠0 := g.bNZ 8
  have fact (i : Fin 10) :
      paired P D*
      (D.d*retEntry P D i 3*P.b (visible i)/P.b 13 -
       D.d*retEntry P D i 1*P.b (visible i)/P.b 11)=
      D.d^4*P.b (visible i)*
        (retEntry P D i 3*Seed.sigma+retEntry P D i 1*(-Seed.sigma)) := by
    rw [paired,g.double]
    field_simp [b13]
    ring
  rw [fact]
  revert i
  apply target_cases
  · intro i
    rw [pair_early,retEntry_early,retEntry_early,ampl_early]
    have eq := Groups.table_pair D.r D.t (Z P D (earlyTarget i)) (D.h i) (pastRead P D i)
    change grouped P D i 3*Seed.sigma+grouped P D i 1*(-Seed.sigma)=D.h i at eq
    rw [eq]
    ring
  · intro i
    have e : Seed.table D.r i 2*Seed.sigma+Seed.table D.r i 0*(-Seed.sigma)=
        (1/2:K)*Seed.pair i+Seed.bary D.r i := by
      rw [← Seed.pair_image g.r0 g.r1 g.r2 i,Fin.sum_univ_three]
      rw [show Seed.pair (0:Fin 3)=-(Seed.sigma:K) by rfl,
        show Seed.pair (1:Fin 3)=(0:K) by rfl,
        show Seed.pair (2:Fin 3)=(Seed.sigma:K) by rfl]
      ring
    rw [show (3:Fin 4)=(2:Fin 3).succ by decide,
      show (1:Fin 4)=(0:Fin 3).succ by decide,retEntry_seed,retEntry_seed,pair_seed P D g,ampl_seed]
    linear_combination (D.d^4*P.b (visible (seedTarget i)))*e
  · simp [physicalPair,show terminal≠(13:Fin 15) by decide,show terminal≠(11:Fin 15) by decide]

theorem actual_pair_ghost (g : Geom P D) (k : Fin 4) :
    mat (Matrix.transpose Aphys) (G P D) (hidden k)=((D.d/2) • G P D+H P D) (hidden k) := by
  have p : hidden k≠13 := by
    intro e
    have h := congrArg Fin.val e
    simp only [hidden_val] at h
    change k.val+1=13 at h
    omega
  have q : hidden k≠11 := by
    intro e
    have h := congrArg Fin.val e
    simp only [hidden_val] at h
    change k.val+1=11 at h
    omega
  have eg : Aphys 13 (hidden k)=Aphys 11 (hidden k) := by
    rw [show (13:Fin 15)=visible 8 by decide,show (11:Fin 15)=visible 6 by decide,
      (feed P D).tableau_nonterminal_tap 8 k (by decide),
      (feed P D).tableau_nonterminal_tap 6 k (by decide)]
    unfold Feed.ghostTap
    change _*(P.mode0 8+P.mode1 8*P.clocks (hidden k))=
      _*(P.mode0 6+P.mode1 6*P.clocks (hidden k))
    rw [g.same0,g.same1]
  rw [G,mat_pair,eg]
  simp [physicalPair,p,q]

theorem sum_eq_origin (v w : V15 K)
    (hs : (∑ i, v i)=(∑ i, w i))
    (hg : ∀ k, v (hidden k)=w (hidden k))
    (hv : ∀ i, v (visible i)=w (visible i)) :
    v 0=w 0 := by
  rw [sum_stages,sum_stages] at hs
  simp_rw [hg,hv] at hs
  exact add_right_cancel hs

@[simp] theorem G_sum : (∑ i : Fin 15, G P D i)=0 := by
  have e := physicalPair_read (paired P D) (1:V15 K)
  simpa [G,row_apply,dotProduct] using e

@[simp] theorem G_hidden (i : Fin 4) :
    G P D (DIRK12MidpointForward.hidden i)=0 := by
  have h (j : Fin 15) (jgt : 4 < j.val) : DIRK12MidpointForward.hidden i≠j := by
    intro e
    have hv := congrArg Fin.val e
    simp only [hidden_val] at hv
    omega
  simp [G,physicalPair,h 11 (by decide),h 13 (by decide)]

theorem live_head (i : Fin 5) (j : Fin 10) :
    live P D (head i) j=P.live (head i) j := by
  unfold live head
  rw [Fin.addCases_left]

/-- The true weighted pair of the assembled physical matrix. This is
an equality of vectors, including the origin filled by the row sums. -/
theorem actual_pair_adjoint (g : Geom P D) :
    mat (Matrix.transpose Aphys) (G P D)=(D.d/2) •G P D+H P D := by
  have p := actual_pair_visible P D g
  have q := actual_pair_ghost P D g
  have l : (∑ i : Fin 15, mat (Matrix.transpose Aphys) (G P D) i)=0 := by
    have c := same_seed_clocks P D g
    simp only [G,mat_pair,← Finset.mul_sum,Finset.sum_sub_distrib]
    have rs (j : Fin 15) : (∑ k, Aphys j k)=nodes Aphys j := by
      simp [nodes,Matrix.mulVec,dotProduct]
    rw [rs,rs,c,sub_self,mul_zero]
  have r : (∑ i : Fin 15, ((D.d/2) • G P D+H P D) i)=0 := by
    have z : ∑ i : Fin 15, G P D i=0 := by
      have e := physicalPair_read (paired P D) (1:V15 K)
      simpa [G,row_apply,dotProduct] using e
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_add_distrib,← Finset.mul_sum,
      z,H_sum,mul_zero,add_zero]
  funext i
  apply stage_cases (P:=fun i =>
    mat (Matrix.transpose Aphys) (G P D) i=((D.d/2) •G P D+H P D) i)
        (sum_eq_origin _ _ (l.trans r.symm) q p) q p i

end RKResearch.Certified.DIRK12MidpointReverse.Physical

#print axioms RKResearch.Certified.DIRK12MidpointReverse.Physical.return_entry
#print axioms RKResearch.Certified.DIRK12MidpointReverse.Physical.terminal_column
#print axioms RKResearch.Certified.DIRK12MidpointReverse.Physical.actual_pair_adjoint
