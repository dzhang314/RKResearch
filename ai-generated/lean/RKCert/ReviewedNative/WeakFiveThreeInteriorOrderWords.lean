module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorCertified
public import Mathlib.Data.List.Permutation
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Logic.Equiv.Fin.Basic

import Mathlib.Tactic.FinCases

@[expose] public section

/-! # Bounded kernel replay of the finite three-interior chronology

The input permutation lists the seven ranks in label order (root 0, root 1,
root 2, u, a, h, z). The original two-rank shard coverage is retained,
but computed only after structural reduction to increasing root triples.
There are 35 groups of 4! tails. No rectangle, determinant, floating-point
computation, or native-decision axiom is involved.
-/
namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

def threeInteriorToken : ThreeInteriorSite ≃ Fin 7 := finSumFinEquiv

def threeInteriorRank (p : List (Fin 7)) (i : ThreeInteriorSite) : Fin 7 :=
  p.getD (threeInteriorToken i).val 0

def threeInteriorRankRoot (p : List (Fin 7)) (i : Fin 3) : Fin 7 :=
  threeInteriorRank p (.inl i)

def threeInteriorRankMark (p : List (Fin 7)) (i : Fin 4) : Fin 7 :=
  threeInteriorRank p (.inr i)

/-- Exact finite sign of a nonzero difference. -/
def threeInteriorRankFactorSign (a b : Fin 7) : ℤ := if a < b then -1 else 1

def threeInteriorRankErasedSign (p : List (Fin 7)) (e j : Fin 4) : ℤ :=
  let x := threeInteriorRankMark p j
  threeInteriorRankFactorSign x (threeInteriorRankMark p e) *
    (threeInteriorRankFactorSign x (threeInteriorRankRoot p 0) *
     threeInteriorRankFactorSign x (threeInteriorRankRoot p 1) *
     threeInteriorRankFactorSign x (threeInteriorRankRoot p 2))

def threeInteriorOrdinalOpposite (p : List (Fin 7)) (leftSide : Bool) (t e : Fin 4) : Prop :=
  ∃ j : Fin 4, j ≠ t ∧ j ≠ e ∧
    ((leftSide = true ∧ threeInteriorRankMark p j < threeInteriorRankMark p t) ∨
     (leftSide = false ∧ threeInteriorRankMark p t < threeInteriorRankMark p j)) ∧
    threeInteriorRankErasedSign p e j * threeInteriorRankErasedSign p e t < 0

instance (p : List (Fin 7)) (leftSide : Bool) (t e : Fin 4) :
    Decidable (threeInteriorOrdinalOpposite p leftSide t e) := by
  unfold threeInteriorOrdinalOpposite
  infer_instance

/-- All local windows and all eight paid opposite-sign tests.
No additional guessed order or separate counting premise is used. -/
def ThreeInteriorOrdinalOK (p : List (Fin 7)) : Prop :=
  let r := threeInteriorRankRoot p
  let m := threeInteriorRankMark p
  r 0 < r 1 ∧ r 1 < r 2 ∧ r 1 < m 0 ∧ m 3 < r 1 ∧
  ((∃ i, m 0 < r i ∧ r i < m 1) ∨ ((∃ i, r i < m 1) ∧ ∃ i, m 1 < r i ∧ r i < m 0)) ∧
  ((∃ i, m 2 < r i ∧ r i < m 3) ∨ ((∃ i, m 2 < r i) ∧ ∃ i, m 3 < r i ∧ r i < m 2)) ∧
  threeInteriorOrdinalOpposite p true 0 1 ∧ threeInteriorOrdinalOpposite p true 0 2 ∧
  threeInteriorOrdinalOpposite p true 0 3 ∧ threeInteriorOrdinalOpposite p true 1 0 ∧
  threeInteriorOrdinalOpposite p false 3 0 ∧ threeInteriorOrdinalOpposite p false 3 1 ∧
  threeInteriorOrdinalOpposite p false 3 2 ∧ threeInteriorOrdinalOpposite p false 2 3

instance (p : List (Fin 7)) : Decidable (ThreeInteriorOrdinalOK p) := by
  unfold ThreeInteriorOrdinalOK
  dsimp only
  infer_instance

def ThreeInteriorWordMatches (p : List (Fin 7)) (w : ThreeInteriorWord) : Prop :=
  ∀ i : Fin 7, threeInteriorRank p (w.labels i) = i

instance (p : List (Fin 7)) (w : ThreeInteriorWord) : Decidable (ThreeInteriorWordMatches p w) := by
  unfold ThreeInteriorWordMatches
  infer_instance

private def publishedWords : List ThreeInteriorWord :=
  [.w0,.w1,.w2,.w3,.w4,.w5,.w6,.w7,.w8]

private def wordDecision (p : List (Fin 7)) : Bool :=
  !decide (ThreeInteriorOrdinalOK p) ||
    publishedWords.any (fun w => decide (ThreeInteriorWordMatches p w))

private def rankShard (a b : Fin 7) : List (List (Fin 7)) :=
  if a < b then
    (((List.finRange 7).erase a).erase b).permutations.map (fun tail => a::b::tail)
  else []

/-- In an admissible word all three root slots are increasing. Use the
structurally recursive permutation enumerator only for the remaining four
marks. Its membership specification is the ordinary `List.Perm`. -/
private def sortedRankShard (a b c : Fin 7) : List (List (Fin 7)) :=
  if a < b then
    if b < c then
      ((((List.finRange 7).erase a).erase b).erase c).permutations'.map
        (fun tail => a :: b :: c :: tail)
    else []
  else []

set_option maxRecDepth 12000
set_option maxHeartbeats 1200000

private theorem sortedShard012 : (sortedRankShard 0 1 2).all wordDecision = true := by
  decide +kernel

private theorem sortedShard013 : (sortedRankShard 0 1 3).all wordDecision = true := by
  decide +kernel

private theorem sortedShard014 : (sortedRankShard 0 1 4).all wordDecision = true := by
  decide +kernel

private theorem sortedShard015 : (sortedRankShard 0 1 5).all wordDecision = true := by
  decide +kernel

private theorem sortedShard016 : (sortedRankShard 0 1 6).all wordDecision = true := by
  decide +kernel

private theorem sortedShard023 : (sortedRankShard 0 2 3).all wordDecision = true := by
  decide +kernel

private theorem sortedShard024 : (sortedRankShard 0 2 4).all wordDecision = true := by
  decide +kernel

private theorem sortedShard025 : (sortedRankShard 0 2 5).all wordDecision = true := by
  decide +kernel

private theorem sortedShard026 : (sortedRankShard 0 2 6).all wordDecision = true := by
  decide +kernel

private theorem sortedShard034 : (sortedRankShard 0 3 4).all wordDecision = true := by
  decide +kernel

private theorem sortedShard035 : (sortedRankShard 0 3 5).all wordDecision = true := by
  decide +kernel

private theorem sortedShard036 : (sortedRankShard 0 3 6).all wordDecision = true := by
  decide +kernel

private theorem sortedShard045 : (sortedRankShard 0 4 5).all wordDecision = true := by
  decide +kernel

private theorem sortedShard046 : (sortedRankShard 0 4 6).all wordDecision = true := by
  decide +kernel

private theorem sortedShard056 : (sortedRankShard 0 5 6).all wordDecision = true := by
  decide +kernel

private theorem sortedShard123 : (sortedRankShard 1 2 3).all wordDecision = true := by
  decide +kernel

private theorem sortedShard124 : (sortedRankShard 1 2 4).all wordDecision = true := by
  decide +kernel

private theorem sortedShard125 : (sortedRankShard 1 2 5).all wordDecision = true := by
  decide +kernel

private theorem sortedShard126 : (sortedRankShard 1 2 6).all wordDecision = true := by
  decide +kernel

private theorem sortedShard134 : (sortedRankShard 1 3 4).all wordDecision = true := by
  decide +kernel

private theorem sortedShard135 : (sortedRankShard 1 3 5).all wordDecision = true := by
  decide +kernel

private theorem sortedShard136 : (sortedRankShard 1 3 6).all wordDecision = true := by
  decide +kernel

private theorem sortedShard145 : (sortedRankShard 1 4 5).all wordDecision = true := by
  decide +kernel

private theorem sortedShard146 : (sortedRankShard 1 4 6).all wordDecision = true := by
  decide +kernel

private theorem sortedShard156 : (sortedRankShard 1 5 6).all wordDecision = true := by
  decide +kernel

private theorem sortedShard234 : (sortedRankShard 2 3 4).all wordDecision = true := by
  decide +kernel

private theorem sortedShard235 : (sortedRankShard 2 3 5).all wordDecision = true := by
  decide +kernel

private theorem sortedShard236 : (sortedRankShard 2 3 6).all wordDecision = true := by
  decide +kernel

private theorem sortedShard245 : (sortedRankShard 2 4 5).all wordDecision = true := by
  decide +kernel

private theorem sortedShard246 : (sortedRankShard 2 4 6).all wordDecision = true := by
  decide +kernel

private theorem sortedShard256 : (sortedRankShard 2 5 6).all wordDecision = true := by
  decide +kernel

private theorem sortedShard345 : (sortedRankShard 3 4 5).all wordDecision = true := by
  decide +kernel

private theorem sortedShard346 : (sortedRankShard 3 4 6).all wordDecision = true := by
  decide +kernel

private theorem sortedShard356 : (sortedRankShard 3 5 6).all wordDecision = true := by
  decide +kernel

private theorem sortedShard456 : (sortedRankShard 4 5 6).all wordDecision = true := by
  decide +kernel

private theorem sortedPair01 (c : Fin 7) :
    (sortedRankShard 0 1 c).all wordDecision = true := by
  fin_cases c
  · rfl
  · rfl
  · exact sortedShard012
  · exact sortedShard013
  · exact sortedShard014
  · exact sortedShard015
  · exact sortedShard016

private theorem sortedPair02 (c : Fin 7) :
    (sortedRankShard 0 2 c).all wordDecision = true := by
  fin_cases c
  · rfl
  · rfl
  · rfl
  · exact sortedShard023
  · exact sortedShard024
  · exact sortedShard025
  · exact sortedShard026

private theorem sortedPair03 (c : Fin 7) :
    (sortedRankShard 0 3 c).all wordDecision = true := by
  fin_cases c
  · rfl
  · rfl
  · rfl
  · rfl
  · exact sortedShard034
  · exact sortedShard035
  · exact sortedShard036

private theorem sortedPair04 (c : Fin 7) :
    (sortedRankShard 0 4 c).all wordDecision = true := by
  fin_cases c
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact sortedShard045
  · exact sortedShard046

private theorem sortedPair05 (c : Fin 7) :
    (sortedRankShard 0 5 c).all wordDecision = true := by
  fin_cases c
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact sortedShard056

private theorem sortedPair06 (c : Fin 7) :
    (sortedRankShard 0 6 c).all wordDecision = true := by
  fin_cases c
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

private theorem sortedPair12 (c : Fin 7) :
    (sortedRankShard 1 2 c).all wordDecision = true := by
  fin_cases c
  · rfl
  · rfl
  · rfl
  · exact sortedShard123
  · exact sortedShard124
  · exact sortedShard125
  · exact sortedShard126

private theorem sortedPair13 (c : Fin 7) :
    (sortedRankShard 1 3 c).all wordDecision = true := by
  fin_cases c
  · rfl
  · rfl
  · rfl
  · rfl
  · exact sortedShard134
  · exact sortedShard135
  · exact sortedShard136

private theorem sortedPair14 (c : Fin 7) :
    (sortedRankShard 1 4 c).all wordDecision = true := by
  fin_cases c
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact sortedShard145
  · exact sortedShard146

private theorem sortedPair15 (c : Fin 7) :
    (sortedRankShard 1 5 c).all wordDecision = true := by
  fin_cases c
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact sortedShard156

private theorem sortedPair16 (c : Fin 7) :
    (sortedRankShard 1 6 c).all wordDecision = true := by
  fin_cases c
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

private theorem sortedPair23 (c : Fin 7) :
    (sortedRankShard 2 3 c).all wordDecision = true := by
  fin_cases c
  · rfl
  · rfl
  · rfl
  · rfl
  · exact sortedShard234
  · exact sortedShard235
  · exact sortedShard236

private theorem sortedPair24 (c : Fin 7) :
    (sortedRankShard 2 4 c).all wordDecision = true := by
  fin_cases c
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact sortedShard245
  · exact sortedShard246

private theorem sortedPair25 (c : Fin 7) :
    (sortedRankShard 2 5 c).all wordDecision = true := by
  fin_cases c
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact sortedShard256

private theorem sortedPair26 (c : Fin 7) :
    (sortedRankShard 2 6 c).all wordDecision = true := by
  fin_cases c
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

private theorem sortedPair34 (c : Fin 7) :
    (sortedRankShard 3 4 c).all wordDecision = true := by
  fin_cases c
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact sortedShard345
  · exact sortedShard346

private theorem sortedPair35 (c : Fin 7) :
    (sortedRankShard 3 5 c).all wordDecision = true := by
  fin_cases c
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact sortedShard356

private theorem sortedPair36 (c : Fin 7) :
    (sortedRankShard 3 6 c).all wordDecision = true := by
  fin_cases c
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

private theorem sortedPair45 (c : Fin 7) :
    (sortedRankShard 4 5 c).all wordDecision = true := by
  fin_cases c
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact sortedShard456

private theorem sortedPair46 (c : Fin 7) :
    (sortedRankShard 4 6 c).all wordDecision = true := by
  fin_cases c
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

private theorem sortedPair56 (c : Fin 7) :
    (sortedRankShard 5 6 c).all wordDecision = true := by
  fin_cases c
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

private theorem all_sorted_shards (a b c : Fin 7) :
    (sortedRankShard a b c).all wordDecision = true := by
  fin_cases a
  · fin_cases b
    · rfl
    · exact sortedPair01 c
    · exact sortedPair02 c
    · exact sortedPair03 c
    · exact sortedPair04 c
    · exact sortedPair05 c
    · exact sortedPair06 c
  · fin_cases b
    · rfl
    · rfl
    · exact sortedPair12 c
    · exact sortedPair13 c
    · exact sortedPair14 c
    · exact sortedPair15 c
    · exact sortedPair16 c
  · fin_cases b
    · rfl
    · rfl
    · rfl
    · exact sortedPair23 c
    · exact sortedPair24 c
    · exact sortedPair25 c
    · exact sortedPair26 c
  · fin_cases b
    · rfl
    · rfl
    · rfl
    · rfl
    · exact sortedPair34 c
    · exact sortedPair35 c
    · exact sortedPair36 c
  · fin_cases b
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact sortedPair45 c
    · exact sortedPair46 c
  · fin_cases b
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact sortedPair56 c
  · fin_cases b
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl

private theorem rankShard_perm {a b : Fin 7} {p : List (Fin 7)}
    (mem : p ∈ rankShard a b) : p.Perm (List.finRange 7) := by
  by_cases hab : a < b
  · rw [rankShard, ite_eq_left hab] at mem
    obtain ⟨tail, ht, rfl⟩ := List.mem_map.mp mem
    let full : List (Fin 7) := List.finRange 7
    have ma : a ∈ full := List.mem_finRange a
    have mb : b ∈ full.erase a :=
      (List.mem_erase_of_ne (ne_of_gt hab)).mpr (List.mem_finRange b)
    have pa : (a :: full.erase a).Perm full := (List.perm_cons_erase ma).symm
    have pb : (b :: (full.erase a).erase b).Perm (full.erase a) :=
      (List.perm_cons_erase mb).symm
    have pt : tail.Perm ((full.erase a).erase b) := List.mem_permutations.mp ht
    exact ((pt.cons b).cons a).trans ((pb.cons a).trans pa)
  · rw [rankShard, ite_eq_right hab] at mem
    exact (List.not_mem_nil mem).elim

/-- The first three entries of a permitted permutation are precisely the
increasing root ranks. Erasing these from the full list leaves exactly the
four tail ranks, in the original labelled order of this permutation. -/
private theorem some_sorted_shard {p : List (Fin 7)} (per : p.Perm (List.finRange 7))
    (h01 : threeInteriorRankRoot p 0 < threeInteriorRankRoot p 1)
    (h12 : threeInteriorRankRoot p 1 < threeInteriorRankRoot p 2) :
    ∃ a b c, p ∈ sortedRankShard a b c := by
  cases p with
  | nil =>
      have hlen := per.length_eq
      simp at hlen
  | cons a rest =>
      cases rest with
      | nil =>
          have hlen := per.length_eq
          simp at hlen
      | cons b rest =>
          cases rest with
          | nil =>
              have hlen := per.length_eq
              simp at hlen
          | cons c tail =>
              change a < b at h01
              change b < c at h12
              refine ⟨a, b, c, ?_⟩
              rw [sortedRankShard, ite_eq_left h01, ite_eq_left h12]
              have p1 := per.erase a
              rw [List.erase_cons_head] at p1
              have p2 := p1.erase b
              rw [List.erase_cons_head] at p2
              have p3 := p2.erase c
              rw [List.erase_cons_head] at p3
              exact List.mem_map.mpr ⟨tail, List.mem_permutations'.mpr p3, rfl⟩

/-- Exact coverage of the original pair shards. No kernel decision has to
reduce their general-purpose permutation enumerator. -/
private theorem all_shards (a b : Fin 7) : (rankShard a b).all wordDecision = true := by
  apply List.all_eq_true.mpr
  intro p hp
  by_cases good : ThreeInteriorOrdinalOK p
  · have h01 : threeInteriorRankRoot p 0 < threeInteriorRankRoot p 1 := good.1
    have h12 : threeInteriorRankRoot p 1 < threeInteriorRankRoot p 2 := good.2.1
    obtain ⟨i, j, k, hk⟩ := some_sorted_shard (rankShard_perm hp) h01 h12
    exact List.all_eq_true.mp (all_sorted_shards i j k) p hk
  · simp only [wordDecision, decide_eq_false good, Bool.not_false, Bool.true_or]

private theorem some_shard {p : List (Fin 7)} (per : p.Perm (List.finRange 7))
    (ordered : threeInteriorRankRoot p 0 < threeInteriorRankRoot p 1) :
    ∃ a b, p ∈ rankShard a b := by
  cases p with
  | nil =>
      have z := per.length_eq
      simp at z
  | cons a rest =>
      cases rest with
      | nil =>
          have z := per.length_eq
          simp at z
      | cons b tail =>
          change a < b at ordered
          refine ⟨a,b,?_⟩
          rw [rankShard,if_pos ordered]
          have one := per.erase a
          rw [List.erase_cons_head] at one
          have two := one.erase b
          rw [List.erase_cons_head] at two
          exact List.mem_map.mpr ⟨tail,List.mem_permutations.mpr two,rfl⟩

theorem threeInterior_finite_order {p : List (Fin 7)} (per : p.Perm (List.finRange 7))
    (data : ThreeInteriorOrdinalOK p) : ∃ w : ThreeInteriorWord, ThreeInteriorWordMatches p w := by
  obtain ⟨a,b,mem⟩ := some_shard per data.1
  have checked := List.all_eq_true.mp (all_shards a b) p mem
  simp only [wordDecision,decide_eq_true data,Bool.not_true,Bool.false_or] at checked
  obtain ⟨w,_,hw⟩ := List.any_eq_true.mp checked
  exact ⟨w,of_decide_eq_true hw⟩

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
