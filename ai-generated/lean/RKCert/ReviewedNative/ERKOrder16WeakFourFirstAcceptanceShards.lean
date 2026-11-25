module

public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstReceiptAssembly
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.List.TakeDrop

@[expose] public section

/-! # Bounded replay checkpoints for the exact weak-four acceptance checks

This module contains no data and does not change the certificate checker.
It splits the original Boolean acceptance equality into bounded clauses.
Stop-specific fitting lists are certified exhaustive by subset and exact
cardinality, not by trusting a generated rank enumeration.
-/
namespace RKCert.ReviewedNative.WeakFourFirstOnly.Replay

open RKCert.ReviewedNative.PolynomialCertificate (checkChain)

universe u

/-- After a small shard has been checked, the remaining suffix is an
independent certificate.  No normalization of other shards is required. -/
theorem stitchAt {α : Type u} {xs : List α} {test : α → Bool} (off width : ℕ)
    (front : ((xs.drop off).take width).all test=true)
    (tail : (xs.drop (off+width)).all test=true) :
    (xs.drop off).all test=true := by
  have tail' : ((xs.drop off).drop width).all test=true := by
    rwa [List.drop_drop]
  calc
    (xs.drop off).all test =
      (((xs.drop off).take width) ++ ((xs.drop off).drop width)).all test :=
        congrArg (fun l => l.all test) (List.take_append_drop width (xs.drop off)).symm
    _ = true := by simp only [List.all_append,front,tail',Bool.and_self]

theorem appendAccepted {α : Type u} {xs ys : List α} {test : α → Bool}
    (x : xs.all test=true) (y : ys.all test=true) :
    (xs++ys).all test=true := by
  simp only [List.all_append,x,y,Bool.and_self]

theorem allPair_left {α : Type u} {L : List α} {f g : α → Bool}
    (test : L.all (fun x => f x && g x)=true) :
    L.all f=true :=
  List.all_eq_true.mpr fun x hx =>
    (Bool.and_eq_true_iff.mp (List.all_eq_true.mp test x hx)).1

theorem allPair_right {α : Type u} {L : List α} {f g : α → Bool}
    (test : L.all (fun x => f x && g x)=true) :
    L.all g=true :=
  List.all_eq_true.mpr fun x hx =>
    (Bool.and_eq_true_iff.mp (List.all_eq_true.mp test x hx)).2

theorem chainAppendAccepted {xs ys : List (ℕ×ℕ)} {start middle finish : ℕ}
    (x : checkChain middle start xs=true)
    (y : checkChain finish middle ys=true) :
    checkChain finish start (xs++ys)=true := by
  induction xs generalizing start with
  | nil =>
    have h : start=middle := of_decide_eq_true x
    simpa only [List.nil_append,h] using y
  | cons ab more ih =>
    rcases ab with ⟨a,b⟩
    have h := Bool.and_eq_true_iff.mp
      (show (decide (start=a ∧ a≤b) && checkChain middle b more)=true from x)
    exact Bool.and_eq_true_iff.mpr ⟨h.1,ih h.2⟩

def ordinaryClaimTest {n m : ℕ} (p : FitClaim (Fin n) n m) : Bool :=
  p.checkAxis && decide (∀ i,
    ordinaryCoordOK p.box i (p.source.band p.rank.1) (p.source.band (p.order i)))

def exteriorClaimTest (P T : List ℚ) (den : ℕ) (high : Bool)
    (p : FitClaim (Option (Fin 7)) 7 4) : Bool :=
  p.checkAxis && decide (∀ i, exteriorCoordOK (den:=den) high p
    (naturalVietaBand high P T p.source den) i)

def frameRankTest {ι : Type u} [DecidableEq ι] [Fintype ι] {n m : ℕ}
    (C : RationalFitCover ι n m) (allowed : ι → Bool) (A : RationalStripFrame n) : Bool :=
  decide (∀ z ∈ allFitRanks m allowed,C.checkPick A z=true)

theorem checkCages_of_checkpoints {ι : Type u} [DecidableEq ι] [Fintype ι] {n m : ℕ}
    {C : RationalFitCover ι n m} {strict : Bool} {P T : List ℚ} {allowed : ι → Bool}
    (den : 0<C.den)
    (chain : checkChain C.den 0 (C.terminal.map RationalStripFrame.span)=true)
    (strips : C.terminal.all (RationalStripFrame.check strict P T C.den)=true)
    (axes : C.claims.all FitClaim.checkAxis=true)
    (picks : C.terminal.all (frameRankTest C allowed)=true) :
    C.checkCages strict P T allowed=true := by
  have h : C.terminal.all
      (fun A => decide (∀ z ∈ allFitRanks m allowed,C.checkPick A z=true))=true := picks
  simp only [RationalFitCover.checkCages,decide_eq_true den,chain,strips,axes,h,Bool.and_self]

theorem ordinaryReceipts_of_checkpoints {n m : ℕ} {C : RationalFitCover (Fin n) n m}
    {P T : List ℚ}
    (den : 0<C.den)
    (chain : checkChain C.den 0 (C.terminal.map RationalStripFrame.span)=true)
    (strips : C.terminal.all (RationalStripFrame.check false P T C.den)=true)
    (data : C.claims.all ordinaryClaimTest=true)
    (picks : C.terminal.all (frameRankTest C (fun _ => true))=true) :
    checkOrdinaryReceipts C P T=true := by
  have d : C.claims.all (fun p => p.checkAxis && decide (∀ i,
      ordinaryCoordOK p.box i (p.source.band p.rank.1) (p.source.band (p.order i))))=true :=
    data
  have h := checkCages_of_checkpoints den chain strips (allPair_left d) picks
  simp only [checkOrdinaryReceipts,h,allPair_right d,Bool.and_self]

theorem exteriorReceipts_of_checkpoints {C : RationalFitCover (Option (Fin 7)) 7 4}
    {P T : List ℚ} {high : Bool}
    (basis : listCoeff P 8=0 ∧ listCoeff P 7≠0 ∧ listCoeff T 8≠0)
    (den : 0<C.den)
    (chain : checkChain C.den 0 (C.terminal.map RationalStripFrame.span)=true)
    (strips : C.terminal.all (RationalStripFrame.check true P T C.den)=true)
    (data : C.claims.all (exteriorClaimTest P T C.den high)=true)
    (picks : C.terminal.all (frameRankTest C (exteriorStopAllowed high))=true) :
    checkExteriorReceipts C P T high=true := by
  have d : C.claims.all (fun p => p.checkAxis && decide (∀ i,
      exteriorCoordOK (den:=C.den) high p (naturalVietaBand high P T p.source C.den) i))=true :=
    data
  have h := checkCages_of_checkpoints den chain strips (allPair_left d) picks
  simp only [checkExteriorReceipts,decide_eq_true basis,h,allPair_right d,Bool.and_self]

structure FitBatch (ι : Type u) where
  stop : ι
  fits : List (Finset ι)

def FitBatch.good {ι : Type u} [DecidableEq ι] [Fintype ι]
    (m : ℕ) (b : FitBatch ι) : Bool :=
  decide (b.fits.Nodup ∧ b.fits.length=Nat.choose (Fintype.card ι-1) m) &&
    b.fits.all (fun I => decide (I.card=m ∧ b.stop∉I))

/-- A stop batch cannot omit any eligible fitting set. -/
theorem FitBatch.complete {ι : Type u} [DecidableEq ι] [Fintype ι]
    {m : ℕ} {b : FitBatch ι} (good : b.good m=true)
    {I : Finset ι} (Ic : I.card=m) (hI : b.stop∉I) : I∈b.fits := by
  have g : (decide (b.fits.Nodup ∧ b.fits.length=Nat.choose (Fintype.card ι-1) m) &&
      b.fits.all (fun I => decide (I.card=m ∧ b.stop∉I)))=true := good
  obtain ⟨shape,rowChecks⟩ := Bool.and_eq_true_iff.mp g
  have h : b.fits.Nodup ∧ b.fits.length=Nat.choose (Fintype.card ι-1) m :=
    of_decide_eq_true shape
  let F := ((Finset.univ : Finset ι).erase b.stop).powersetCard m
  have sub : b.fits.toFinset ⊆ F := by
    intro U hU
    have tests : U.card=m ∧ b.stop∉U :=
      of_decide_eq_true (List.all_eq_true.mp rowChecks U (List.mem_toFinset.mp hU))
    apply Finset.mem_powersetCard.mpr
    refine ⟨?_,tests.1⟩
    intro x hx
    exact Finset.mem_erase.mpr ⟨fun e => tests.2 (e ▸ hx),Finset.mem_univ _⟩
  have hc : F.card ≤ b.fits.toFinset.card := by
    dsimp only [F]
    rw [Finset.card_powersetCard,Finset.card_erase_of_mem (Finset.mem_univ b.stop),
      Finset.card_univ,List.toFinset_card_of_nodup h.1,h.2]
  have eq := Finset.eq_of_subset_of_card_le sub hc
  apply List.mem_toFinset.mp
  rw [eq]
  apply Finset.mem_powersetCard.mpr
  refine ⟨?_,Ic⟩
  intro x hx
  exact Finset.mem_erase.mpr ⟨fun e => hI (e ▸ hx),Finset.mem_univ _⟩

def batchPlanCheck {ι : Type u} [DecidableEq ι] [Fintype ι]
    (m : ℕ) (allowed : ι → Bool) (plan : List (FitBatch ι)) : Bool :=
  plan.all (FitBatch.good m) &&
    decide (∀ j : ι, allowed j=true → plan.any (fun b => decide (b.stop=j))=true)

def FitBatch.pickTest {ι : Type u} [DecidableEq ι] {n m : ℕ}
    (C : RationalFitCover ι n m) (A : RationalStripFrame n) (b : FitBatch ι) : Bool :=
  b.fits.all (fun I => C.checkPick A (b.stop,I))

/-- The outer lookup into the terminal-guide table is checked once per
terminal. The inner rank shards do not traverse that large table again. -/
def scopedPickTest {ι : Type u} [DecidableEq ι] {n m : ℕ}
    (C : RationalFitCover ι n m) (A : RationalStripFrame n)
    (guide : FitRank ι → Option ℕ) (z : FitRank ι) : Bool :=
  match (guide z).bind (fun i => C.claims[i]?) with
  | none => false
  | some p => decide (p.rank=z) && A.subCheck p.source

theorem scopedPickTest_eq {ι : Type u} [DecidableEq ι] {n m : ℕ}
    {C : RationalFitCover ι n m} {A : RationalStripFrame n}
    {guide : FitRank ι → Option ℕ} (fixGuide : C.guide A.span.1=guide)
    (z : FitRank ι) : scopedPickTest C A guide z=C.checkPick A z := by
  simp only [scopedPickTest, RationalFitCover.checkPick, RationalFitCover.pick, fixGuide] <;> rfl

theorem FitBatch.pickTest_of_scoped {ι : Type u} [DecidableEq ι] {n m : ℕ}
    {C : RationalFitCover ι n m} {A : RationalStripFrame n}
    {g : FitRank ι → Option ℕ} {row : FitBatch ι}
    (fixed : C.guide A.span.1=g)
    (tests : row.fits.all (fun I => scopedPickTest C A g (row.stop,I))=true) :
    row.pickTest C A=true := by
  simpa only [FitBatch.pickTest,scopedPickTest_eq fixed] using tests

theorem frameRankTest_of_batch_checkpoints {ι : Type u} [DecidableEq ι] [Fintype ι] {n m : ℕ}
    {C : RationalFitCover ι n m} {A : RationalStripFrame n}
    {allowed : ι → Bool} {plan : List (FitBatch ι)}
    (valid : batchPlanCheck m allowed plan=true)
    (c : plan.all (FitBatch.pickTest C A)=true) :
    frameRankTest C allowed A=true := by
  have vp : (plan.all (FitBatch.good m) &&
      decide (∀ j : ι, allowed j=true → plan.any (fun b => decide (b.stop=j))=true))=true :=
    valid
  obtain ⟨s,b⟩ := Bool.and_eq_true_iff.mp vp
  have present : ∀ j : ι, allowed j=true → plan.any (fun b => decide (b.stop=j))=true :=
    of_decide_eq_true b
  unfold frameRankTest
  apply decide_eq_true
  rintro ⟨j,I⟩ z
  obtain ⟨product,notI,okay⟩ := Finset.mem_filter.mp z
  have d : I.card=m := (Finset.mem_powersetCard.mp (Finset.mem_product.mp product).2).2
  obtain ⟨row,hrow,atStop⟩ := List.any_eq_true.mp (present j okay)
  have stop : row.stop=j := of_decide_eq_true atStop
  have ins : I∈row.fits := FitBatch.complete (List.all_eq_true.mp s row hrow) d
    (by simpa only [stop] using notI)
  have got : row.fits.all (fun J => C.checkPick A (row.stop,J))=true :=
    List.all_eq_true.mp c row hrow
  simpa only [stop] using List.all_eq_true.mp got I ins

end RKCert.ReviewedNative.WeakFourFirstOnly.Replay
