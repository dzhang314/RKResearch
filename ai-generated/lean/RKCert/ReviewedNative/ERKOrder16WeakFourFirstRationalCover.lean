module

public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstAxisReceipt
public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstReferenceLists
public import RKCert.ReviewedNative.PolynomialCertificateDyadicCover
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.NormNum

@[expose] public section

/-! # Uniform finite rational box receipts for the weak-four first port

A chart uses one terminal partition per polynomial pencil. A rank's signed
box may have been checked higher in the tree; the checker verifies containment
of the terminal rectangle in that source rectangle. The role enumeration
is a full finite powerset, not a list of sampled or pre-filtered fibres.
-/
namespace RKCert.ReviewedNative.WeakFourFirstOnly

open Polynomial Set
open RKCert.ReviewedNative.PolynomialBracket (ofCoeffs horner eval₂_ofCoeffs)
open RKCert.ReviewedNative.OrderedPolynomialSignStrips
open RKCert.ReviewedNative.OrderedRootGapSaturation (OrderedExtension)
open RKCert.ReviewedNative.FiniteRootSeparator (eval_on_base)
open RKCert.ReviewedNative.PolynomialCertificate (checkChain checkChain_covers gridCoord
  gridCoord_strictMono)
open scoped BigOperators

universe u

def rationalPencilValue (P T : List ℚ) (v x : ℚ) : ℚ :=
  (1-v)*horner P x+v*horner T x

structure RationalStripFrame (n : ℕ) where
  span : ℕ × ℕ
  lower : Fin n → ℚ
  upper : Fin n → ℚ
  rising : Fin n → Bool

def RationalStripFrame.check (strict : Bool) (P T : List ℚ) (den : ℕ)
    {n : ℕ} (A : RationalStripFrame n) : Bool :=
  let p := rationalPencilValue P T (gridCoord den A.span.1)
  let q := rationalPencilValue P T (gridCoord den A.span.2)
  decide ((∀ i, A.lower i ≤ A.upper i) ∧
    (∀ i j, i < j → A.upper i < A.lower j) ∧
    (∀ i, if strict then 0<A.lower i ∧ A.upper i<1 else 0≤A.lower i ∧ A.upper i≤1) ∧
    (∀ i, if A.rising i then
      (p (A.lower i)≤0 ∧ q (A.lower i)≤0) ∧
        (0≤p (A.upper i) ∧ 0≤q (A.upper i))
      else
      (0≤p (A.lower i) ∧ 0≤q (A.lower i)) ∧
        (p (A.upper i)≤0 ∧ q (A.upper i)≤0)))

def RationalStripFrame.subCheck {n : ℕ} (A B : RationalStripFrame n) : Bool :=
  decide (B.span.1≤A.span.1 ∧ A.span.2≤B.span.2 ∧
    ∀ i, B.lower i≤A.lower i ∧ A.upper i≤B.upper i)

noncomputable section
variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def RationalStripFrame.param {n : ℕ} (den : ℕ) (A : RationalStripFrame n) (v : K) : Prop :=
  v ∈ Icc (gridCoord den A.span.1) (gridCoord den A.span.2)

def RationalStripFrame.nodes {n : ℕ} (A : RationalStripFrame n) (r : Fin n → K) : Prop :=
  ∀ i, r i ∈ Icc (A.lower i:K) (A.upper i:K)

theorem RationalStripFrame.param_of_subCheck {n den : ℕ} {A B : RationalStripFrame n}
    (dn : 0<den) (s : A.subCheck B = true) {v : K} (hv : A.param den v) :
    B.param den v := by
  have h : B.span.1≤A.span.1 ∧ A.span.2≤B.span.2 ∧
      ∀ i, B.lower i≤A.lower i ∧ A.upper i≤B.upper i := of_decide_eq_true s
  have hg := (gridCoord_strictMono (K:=K) dn).monotone
  exact ⟨(hg h.1).trans hv.1,hv.2.trans (hg h.2.1)⟩

theorem RationalStripFrame.nodes_of_subCheck {n : ℕ} {A B : RationalStripFrame n}
    (s : A.subCheck B = true) {r : Fin n → K} (hr : A.nodes r) : B.nodes r := by
  have h : B.span.1≤A.span.1 ∧ A.span.2≤B.span.2 ∧
      ∀ i, B.lower i≤A.lower i ∧ A.upper i≤B.upper i := of_decide_eq_true s
  intro i
  exact ⟨(Rat.cast_le.mpr (h.2.2 i).1).trans (hr i).1,
    (hr i).2.trans (Rat.cast_le.mpr (h.2.2 i).2)⟩

private theorem gridCoord_cast (den i : ℕ) : ((gridCoord (K:=ℚ) den i : ℚ):K)=
    gridCoord (K:=K) den i := by
  simp only [gridCoord,Rat.cast_div,Rat.cast_natCast]

private theorem rational_pencil_eval_cast (P T : List ℚ) (den i : ℕ) (x : ℚ) :
    (pencil ((ofCoeffs P).map (Rat.castHom K)) ((ofCoeffs T).map (Rat.castHom K))
      (gridCoord den i)).eval (x:K) = (rationalPencilValue P T (gridCoord den i) x:K) := by
  let f : ℚ →+* K := Rat.castHom K
  have evalZ (A : List ℚ) : ((ofCoeffs A).map f).eval (x:K) = f (horner A x) := by
    change ((ofCoeffs A).map f).eval (f x) = _
    rw [eval_on_base]
    have h : (ofCoeffs A).eval x = horner A x := by
      simpa only [eval₂_id,RingHom.coe_id,List.map_id] using eval₂_ofCoeffs (RingHom.id ℚ) A x
    rw [h]
  rw [pencil_eval,evalZ P,evalZ T,←gridCoord_cast (K:=K) den i]
  let q : ℚ := gridCoord den i
  change (1-f q)*f (horner P x)+f q*f (horner T x) = f (rationalPencilValue P T q x)
  simp only [rationalPencilValue,map_add,map_mul,map_sub,map_one]

theorem RationalStripFrame.strips_of_check {strict : Bool} {P T : List ℚ} {den n : ℕ}
    {A : RationalStripFrame n} (ok : A.check strict P T den=true)
    {v : K} (hv : A.param den v) :
    SignStrips (pencil ((ofCoeffs P).map (Rat.castHom K)) ((ofCoeffs T).map (Rat.castHom K)) v)
      (fun i => (A.lower i:K)) (fun i => (A.upper i:K)) ∧
    (∀ i, if strict then (0:K)<(A.lower i:K) ∧ (A.upper i:K)<1
      else (0:K)≤(A.lower i:K) ∧ (A.upper i:K)≤1) := by
  let p := rationalPencilValue P T (gridCoord den A.span.1)
  let q := rationalPencilValue P T (gridCoord den A.span.2)
  have h : (∀ i, A.lower i ≤ A.upper i) ∧
    (∀ i j, i < j → A.upper i < A.lower j) ∧
    (∀ i, if strict then 0<A.lower i ∧ A.upper i<1 else 0≤A.lower i ∧ A.upper i≤1) ∧
    (∀ i, if A.rising i then
      (p (A.lower i)≤0 ∧ q (A.lower i)≤0) ∧
        (0≤p (A.upper i) ∧ 0≤q (A.upper i))
      else
      (0≤p (A.lower i) ∧ 0≤q (A.lower i)) ∧
        (p (A.upper i)≤0 ∧ q (A.upper i)≤0)) := of_decide_eq_true ok
  have C : PencilCell ((ofCoeffs P).map (Rat.castHom K)) ((ofCoeffs T).map (Rat.castHom K))
      (gridCoord den A.span.1) (gridCoord den A.span.2)
      (fun i => (A.lower i:K)) (fun i => (A.upper i:K)) := by
    refine ⟨fun i => Rat.cast_le.mpr (h.1 i),
      fun {i j} ij => Rat.cast_lt.mpr (h.2.1 i j ij),?_⟩
    intro i
    simp only [rational_pencil_eval_cast]
    have s := h.2.2.2 i
    by_cases b : A.rising i
    · apply Or.inl
      simp only [b,if_true] at s
      exact_mod_cast s
    · apply Or.inr
      simp only [b,if_false] at s
      exact_mod_cast s
  refine ⟨C.at_param hv.1 hv.2,?_⟩
  intro i
  have b := h.2.2.1 i
  cases strict <;> simp only [Bool.false_eq_true,if_false,if_true] at b ⊢ <;> exact_mod_cast b

end

abbrev FitRank (ι : Type*) := ι × Finset ι

def allFitRanks {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ℕ)
    (allowed : ι → Bool) : Finset (FitRank ι) :=
  ((Finset.univ : Finset ι).product ((Finset.univ : Finset ι).powersetCard m)).filter
    (fun z => z.1∉z.2 ∧ allowed z.1=true)

theorem mem_allFitRanks {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
    {allowed : ι → Bool} {j : ι} {I : Finset ι} (c : I.card=m) (jm : j∉I)
    (good : allowed j=true) : (j,I)∈allFitRanks m allowed := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _,
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,c⟩⟩,jm,good⟩

structure FitClaim (ι : Type*) (n m : ℕ) where
  source : RationalStripFrame n
  rank : FitRank ι
  order : Fin m → ι
  box : AxisBox m

abbrev FitClaim.isAligned {ι : Type*} [DecidableEq ι] [Fintype ι] {n m : ℕ}
    (p : FitClaim ι n m) : Prop :=
  (∀ i k, p.order i=p.order k → i=k) ∧
  (∀ j, j∈p.rank.2 ↔ ∃ i, p.order i=j)

def FitClaim.checkAxis {ι : Type*} [DecidableEq ι] [Fintype ι] {n m : ℕ}
    (p : FitClaim ι n m) : Bool :=
  decide p.isAligned && p.box.check

noncomputable def FitClaim.decodeOrder {ι : Type*} [DecidableEq ι] [Fintype ι] {n m : ℕ}
    (p : FitClaim ι n m) (a : p.isAligned) : Fin m ≃ {i // i∈p.rank.2} := by
  let f : Fin m → {i // i∈p.rank.2} := fun i =>
    ⟨p.order i,(a.2 _).2 ⟨i,rfl⟩⟩
  refine Equiv.ofBijective f ⟨?_,?_⟩
  · intro i j h
    exact a.1 i j (congrArg Subtype.val h)
  · intro j
    obtain ⟨i,h⟩ := (a.2 j.val).1 j.property
    exact ⟨i,Subtype.ext h⟩

@[simp] theorem FitClaim.decodeOrder_val {ι : Type*} [DecidableEq ι] [Fintype ι] {n m : ℕ}
    (p : FitClaim ι n m) (a : p.isAligned) (i : Fin m) :
    (p.decodeOrder a i).val=p.order i := rfl

/-- The input may split claims into independent chunks. A flattened tree leaf
only needs the ancestor sources containing its sustained roles. The selector
below does not trust the witness indices or the alignment of a certificate. -/
structure RationalFitCover (ι : Type*) (n m : ℕ) where
  den : ℕ
  terminal : List (RationalStripFrame n)
  claims : List (FitClaim ι n m)
  /-- Untrusted index into claims, selected by terminal start and rank.
  Soundness tests the selected rank and both box containments. -/
  guide : ℕ → FitRank ι → Option ℕ

def RationalFitCover.pick {ι : Type*} {n m : ℕ} (C : RationalFitCover ι n m)
    (A : RationalStripFrame n) (z : FitRank ι) : Option (FitClaim ι n m) :=
  (C.guide A.span.1 z).bind fun i => C.claims[i]?

def RationalFitCover.checkPick {ι : Type*} [DecidableEq ι] {n m : ℕ}
    (C : RationalFitCover ι n m) (A : RationalStripFrame n) (z : FitRank ι) : Bool :=
  match C.pick A z with
  | none => false
  | some p => decide (p.rank=z) && A.subCheck p.source

theorem RationalFitCover.pick_mem {ι : Type*} {n m : ℕ} {C : RationalFitCover ι n m}
    {A : RationalStripFrame n} {z : FitRank ι} {p : FitClaim ι n m}
    (H : C.pick A z=some p) : p∈C.claims := by
  cases w : C.guide A.span.1 z with
  | none => simp [RationalFitCover.pick,w] at H
  | some i =>
    have h : C.claims[i]?=some p := by simpa [RationalFitCover.pick,w] using H
    exact List.mem_of_getElem? h

def RationalFitCover.checkCages {ι : Type*} [DecidableEq ι] [Fintype ι] {n m : ℕ}
    (C : RationalFitCover ι n m) (strict : Bool) (P T : List ℚ) (allowed : ι → Bool) : Bool :=
  decide (0<C.den) &&
  checkChain C.den 0 (C.terminal.map RationalStripFrame.span) &&
  C.terminal.all (RationalStripFrame.check strict P T C.den) &&
  C.claims.all FitClaim.checkAxis &&
  C.terminal.all (fun A => decide (∀ z∈allFitRanks m allowed,C.checkPick A z=true))

noncomputable section
variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem RationalFitCover.find_terminal {ι : Type*} [DecidableEq ι] [Fintype ι] {n m : ℕ}
    {C : RationalFitCover ι n m} {strict : Bool} {P T : List ℚ} {allowed : ι → Bool}
    (ok : C.checkCages strict P T allowed=true) {v : K} (h : v∈Icc (0:K) 1) :
    ∃ A∈C.terminal, A.param C.den v ∧
      A.check strict P T C.den=true ∧
      ∀ z∈allFitRanks m allowed, ∃ p∈C.claims,
        p.rank=z ∧ p.isAligned ∧ p.box.check=true ∧ A.subCheck p.source=true := by
  have b := ok
  simp only [RationalFitCover.checkCages,Bool.and_eq_true_iff] at b
  obtain ⟨⟨⟨⟨den,chain⟩,geom⟩,axes⟩,cover⟩ := b
  have dp : 0<C.den := of_decide_eq_true den
  have nd : (C.den:K) ≠ 0 := (Nat.cast_pos.mpr dp).ne'
  have h' : v∈Icc (gridCoord (K:=K) C.den 0) (gridCoord C.den C.den) := by
    simpa only [gridCoord,Nat.cast_zero,zero_div,div_self nd] using h
  obtain ⟨span,mem,hs⟩ := checkChain_covers (gridCoord (K:=K) C.den)
    (gridCoord_strictMono dp) _ dp chain h'
  obtain ⟨A,hA,rfl⟩ := List.mem_map.mp mem
  refine ⟨A,hA,hs,List.all_eq_true.mp geom _ hA,?_⟩
  intro rank hrank
  have checkedRoles : ∀ z∈allFitRanks m allowed,C.checkPick A z=true :=
    of_decide_eq_true (List.all_eq_true.mp cover _ hA)
  have hit := checkedRoles rank hrank
  cases s : C.pick A rank with
  | none => simp [RationalFitCover.checkPick,s] at hit
  | some p =>
    have hp := RationalFitCover.pick_mem s
    have pair : (decide (p.rank=rank) && A.subCheck p.source)=true := by
      simpa only [RationalFitCover.checkPick,s] using hit
    obtain ⟨role,sub⟩ := Bool.and_eq_true_iff.mp pair
    obtain ⟨align,axis⟩ := Bool.and_eq_true_iff.mp
      (show p.checkAxis=true from List.all_eq_true.mp axes p hp)
    exact ⟨p,hp,of_decide_eq_true role,of_decide_eq_true align,axis,sub⟩

/-- A source's factor normalization verifies the selected interval for each
coordinate, without making any assumption on a value of the paid integral. -/
def FitClaim.Coordinates {ι : Type*} {n m : ℕ} (p : FitClaim ι n m)
    (r : ι → K) : Prop :=
  ∃ x scale : Fin m → K,
    (∀ i, x i ∈ Icc (p.box.lower i:K) (p.box.upper i:K)) ∧
    (∀ i, scale i≠0) ∧
    (∀ i, C (r p.rank.1)*X-C (r (p.order i))=
      C (scale i)*(p.box.forms i).poly (x i))

theorem FitClaim.not_paid {ι : Type*} [DecidableEq ι] [Fintype ι] {n m : ℕ}
    (p : FitClaim ι n m) (a : p.isAligned) (b : p.box.check=true)
    {r : ι → K} (coordinates : p.Coordinates r) :
    ¬ UnitPair (stoppedFactors r p.rank.2 (r p.rank.1)) := by
  obtain ⟨x,scale,w,nonzero,form⟩ := coordinates
  exact p.box.rejects_finite_fit b p.rank.2 r (r p.rank.1) (p.decodeOrder a) x scale
    w nonzero (by simpa only [FitClaim.decodeOrder_val] using form)

private theorem castNodes_of_orderedExtension {n : ℕ} (E : OrderedExtension K)
    (A : RationalStripFrame n) (r : Fin n → E.carrier)
    (h : ∀ i, E.embed (A.lower i:K)≤r i ∧ r i≤E.embed (A.upper i:K)) : A.nodes r := by
  intro i
  apply Set.mem_Icc.mpr
  simpa only [map_ratCast] using h i

/-- Reuse the one generic finite selector for cubic and all-interior quartic
receipts. The only per-row lemma to supply concerns ratios of actual roots
and their exact factor normalizations, not a local integral. -/
theorem interiorCover_of_rational_receipt {n m : ℕ} {P T : List ℚ}
    (S : RationalFitCover (Fin n) n m) (den : 0<S.den)
    (check : S.checkCages false P T (fun _ => true)=true)
    (normalize : ∀ (E : OrderedExtension K) (p : FitClaim (Fin n) n m), p∈S.claims →
      ∀ r : Fin n → E.carrier, p.source.nodes r → 0<r p.rank.1 → p.Coordinates r) :
    InteriorCover ((ofCoeffs P).map (Rat.castHom K)) ((ofCoeffs T).map (Rat.castHom K)) n m := by
  intro v v0 v1
  obtain ⟨A,_,vv,geometry,claims⟩ := RationalFitCover.find_terminal check ⟨v0,v1⟩
  obtain ⟨strips,h⟩ := A.strips_of_check geometry vv
  refine ⟨fun i => (A.lower i:K),fun i => (A.upper i:K),strips,?_ ,?_⟩
  · simpa only [Bool.false_eq_true,if_false] using h
  · intro E r cage I Icard j jm pos
    have Hr := castNodes_of_orderedExtension E A r cage
    have m := mem_allFitRanks Icard jm (allowed:=fun _ => true) rfl
    obtain ⟨p,hp,role,align,axis,sub⟩ := claims _ m
    have coords := normalize E p hp r (RationalStripFrame.nodes_of_subCheck sub Hr)
      (by simpa only [role] using pos)
    simpa only [role] using p.not_paid align axis coords

def exteriorStopAllowed (high : Bool) : Option (Fin 7) → Bool
  | none => high
  | some _ => true

theorem exteriorCover_of_rational_receipt {P T : List ℚ} {high : Bool}
    (S : RationalFitCover (Option (Fin 7)) 7 4) (den : 0<S.den)
    (check : S.checkCages true P T (exteriorStopAllowed high)=true)
    (normalize : ∀ (E : OrderedExtension K) (p : FitClaim (Option (Fin 7)) 7 4),
      p∈S.claims → ∀ v : K, p.source.param S.den v →
      ∀ (r : Fin 7 → E.carrier) (e : E.carrier),
      p.source.nodes r → (if high then 1≤e else e≤0) →
      let F := (pencil ((ofCoeffs P).map (Rat.castHom K)) ((ofCoeffs T).map (Rat.castHom K)) v).map E.embed
      F.coeff 7 = -(F.coeff 8)*(e+∑ i : Fin 7,r i) →
      0<withExtra r e p.rank.1 → p.Coordinates (withExtra r e)) :
    ExteriorCover ((ofCoeffs P).map (Rat.castHom K)) ((ofCoeffs T).map (Rat.castHom K)) high := by
  intro v v0 v1
  obtain ⟨A,_,vv,geom,claims⟩ := RationalFitCover.find_terminal check ⟨v0,v1⟩
  obtain ⟨strips,bounds⟩ := A.strips_of_check geom vv
  refine ⟨fun i => (A.lower i:K),fun i => (A.upper i:K),strips,?_,?_⟩
  · simpa only [if_true] using bounds
  · intro E r e cage side vieta I Ic j jm jp
    have Hr := castNodes_of_orderedExtension E A r cage
    have allowed : exteriorStopAllowed high j=true := by
      cases j with
      | some i => rfl
      | none =>
        cases high
        · exact (not_lt_of_ge side jp).elim
        · rfl
    obtain ⟨p,hp,role,align,axis,sub⟩ := claims (j,I) (mem_allFitRanks Ic jm allowed)
    have coords := normalize E p hp v (RationalStripFrame.param_of_subCheck den sub vv)
      r e (RationalStripFrame.nodes_of_subCheck sub Hr) side vieta (by simpa only [role] using jp)
    simpa only [role] using p.not_paid align axis coords

/-- The four proof products exactly match the structural reference packet. -/
theorem firstBoxCover_of_four_rational_covers
    (A : InteriorCover (firstReferenceJ K) (firstReferenceJ K) 7 3)
    (B : InteriorCover (firstReferenceP₀ K) (firstReferenceP₁ K) 8 4)
    (C : ExteriorCover (firstReferenceJ K) (firstReferenceP₀ K) false)
    (D : ExteriorCover (firstReferenceJ K) (-firstReferenceP₁ K) true) :
    FirstBoxCover (firstReferenceJ K) (firstReferenceP₀ K) (firstReferenceP₁ K) :=
  ⟨A,B,C,D⟩

end
end RKCert.ReviewedNative.WeakFourFirstOnly
