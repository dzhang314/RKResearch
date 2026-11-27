module

public import RKCert.ReviewedNative.ERKOrderEightFourOffPhysicalPlacement
public import RKCert.ReviewedNative.ERK8FourOffCleanPrimitive

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

@[expose] public section

/-! # The actual k,6,7 clean primitive placement for four off clocks

This combines the measured Marked placement with the checked clean-root
probe decoder. It uses neither a terminal profile nor a Newton equation,
and does not repeat the geometric clean shape computation.
-/
namespace RKResearch.Certified.Graded.FourOffNewton

open Polynomial RKResearch OneOff ERKTaggedHorizon FourOffPhysical ERK8PaidField RKCert.Endpoint
open RKResearch.Certified.Graded.MultiOff.FourOff8CleanShape
open RKResearch.Certified.Graded.MultiOff.FourOff8Scalar
open scoped Matrix Classical

variable {K : Type*} [Field K]
variable {A : Matrix (Fin 10) (Fin 10) K} {b : Fin 10 → K} {P : K[X]} {dup k : Fin 10}

private theorem marked_k_before_six (M : Placement A b P dup k) : k<6 := by
  have h := M.firstAtFourOrFive
  omega

private theorem marked_clean_prefix_six (M : Placement A b P dup k)
    {j : Fin 10} (hj : j<6) (gj : g A j=0) :
    nodes A j=0 ∨ nodes A j=nodes A k := by
  by_cases e : j=0
  · left
    rw [e,M.rankData.clockZero]
  · right
    have pos : (0:Fin 10)<j := lt_of_le_of_ne (Fin.zero_le _) (fun h => e h.symm)
    rw [M.onlyCleanInMiddle j pos hj gj]

private theorem marked_clean_before_eight (M : Placement A b P dup k)
    {j : Fin 10} (hj : j<8) (gj : g A j=0) :
    nodes A j=0 ∨ nodes A j=nodes A k ∨ nodes A j=nodes A 6 ∨ nodes A j=nodes A 7 := by
  by_cases j6 : j<6
  · rcases marked_clean_prefix_six M j6 gj with h|h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · have cases : j=6 ∨ j=7 := by omega
    rcases cases with rfl|rfl
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))

/-- The late duplicate is propagated on the clean tag only. A coincident
off clock must not be used to infer an extra clean occurrence. -/
theorem marked_clean_value_census (M : Placement A b P dup k) (j : Fin 10) (gj : g A j=0) :
    nodes A j=0 ∨ nodes A j=nodes A k ∨ nodes A j=nodes A 6 ∨
      nodes A j=nodes A 7 ∨ nodes A j=1 := by
  have lift {u : K} (h : u=0 ∨ u=nodes A k ∨ u=nodes A 6 ∨ u=nodes A 7) :
      u=0 ∨ u=nodes A k ∨ u=nodes A 6 ∨ u=nodes A 7 ∨ u=1 := by
    rcases h with h|h|h|h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  by_cases early : j<8
  · exact lift (marked_clean_before_eight M early gj)
  · have late : j=8 ∨ j=9 := by omega
    rcases late with rfl|rfl
    · have same := M.repeatAtEight.same
      rw [←same.1]
      exact lift (marked_clean_before_eight M M.repeatAtEight.before (same.2.mpr gj))
    · exact Or.inr (Or.inr (Or.inr (Or.inr M.rankData.clockNine)))

private theorem clean_clock_inj_before_eight (M : Placement A b P dup k)
    {i j : Fin 10} (i8 : i<8) (j8 : j<8) (gi : g A i=0) (gj : g A j=0)
    (h : nodes A i=nodes A j) : i=j := by
  have same : SameTag A i j := ⟨h,iff_of_true gi gj⟩
  by_contra ne
  rcases lt_or_gt_of_ne ne with lt|lt
  · exact (ne_of_lt j8) (M.repeatAtEight.unique lt same).2
  · exact (ne_of_lt i8) (M.repeatAtEight.unique lt same.symm).2

/-- Expose the cubic identity already paid in the existing census route,
but not part of its public branch-existence signature. No node order
or POS assumption is used: the probes use aggregate off cancellation. -/
theorem marked_paid_clean_cubic (ho : HasOrder 8 A b) (M : Placement A b P dup k) :
    nodalHull (((cleanKnots A).erase 1).erase 0) = (LobattoEight.lobattoCubic : K[X]) := by
  let T := (cleanKnots A).erase 1
  let S := T.erase 0
  let L := nodalHull S
  have zero : (0:K)∈cleanKnots A := mem_cleanKnots.mpr ⟨0,M.rankData.cleanZero,M.rankData.clockZero⟩
  have one : (1:K)∈cleanKnots A := mem_cleanKnots.mpr ⟨9,M.rankData.cleanNine,M.rankData.clockNine⟩
  have zT : (0:K)∈T := Finset.mem_erase.mpr ⟨zero_ne_one,zero⟩
  have tc : T.card=4 := by
    change ((cleanKnots A).erase 1).card=4
    rw [Finset.card_erase_of_mem one,M.rankData.cleanCard]
  have sc : S.card=3 := by
    change (T.erase 0).card=3
    rw [Finset.card_erase_of_mem zT,tc]
  have ld : L.natDegree=3 := (natDegree_nodalHull S).trans sc
  have beta := beta_cubic_from_probes_paid ho L ld.le (fun j=>by
    have factor {U : Finset K} {a : K} (ha : a∈U) :
        nodalHull U=(X-C a)*nodalHull (U.erase a) := by
      unfold nodalHull
      exact (Finset.mul_prod_erase U (fun u : K => (X:K[X])-C u) ha).symm
    have first : nodalHull (cleanKnots A)=(X-C (1:K))*nodalHull T := factor one
    have next : nodalHull T=(X-C (0:K))*L := factor zT
    have fac : nodalHull (cleanKnots A)=((X:K[X])^2-X)*L := by
      rw [first,next]
      simp only [map_one,map_zero,sub_zero]
      ring
    change probe A b j.val (evalNodes A (((X:K[X])^2-X)*L))=0
    rw [←fac]
    exact probe_zero_of_clean_roots M.rankData.cancel _ (fun _ hx=>nodalHull_eval_of_mem hx) j.val)
  have lc : L.coeff 3=1 := by
    rw [←ld]
    exact (monic_nodalHull S).coeff_natDegree
  simpa only [lc,map_one,one_mul] using beta

private theorem scalar_root_of_cubic (ho : HasOrder 8 A b) {u : K}
    (r : (LobattoEight.lobattoCubic : K[X]).eval u=0) :
    lobattoNumer u=0 := by
  have d0 : ((-1:K)/14)*14=-1 := div_mul_cancel₀ _ (fourteen_ne ho)
  have d1 : ((9:K)/14)*14=9 := div_mul_cancel₀ _ (fourteen_ne ho)
  have d2 : ((-3:K)/2)*2=-3 := div_mul_cancel₀ _ (two_ne ho)
  simp only [LobattoEight.lobattoCubic,eval_add,eval_monomial,
    pow_zero,pow_one,mul_one,one_mul] at r
  unfold lobattoNumer
  linear_combination 14*r-d0-u*d1-7*u^2*d2

theorem marked_actual_clean_geometry (ho : HasOrder 8 A b) (M : Placement A b P dup k) :
    CleanClocks (nodes A k) (nodes A 6) (nodes A 7) ∧
      quartic (nodes A k) (nodes A 6) (nodes A 7)=(X:K[X])*LobattoEight.lobattoCubic := by
  let h := nodes A k
  let x := nodes A 6
  let z := nodes A 7
  let S := ((cleanKnots A).erase 1).erase 0
  have k6 := marked_k_before_six M
  have k7 : k<7 := k6.trans (by decide)
  have k8 : k<8 := k6.trans (by decide)
  have k9 : k≠9 := ne_of_lt (k6.trans (by decide : (6:Fin 10)<9))
  have hx : h≠x := fun eq=>(ne_of_lt k6)
    (clean_clock_inj_before_eight M k8 (by decide) M.firstClean M.cleanSix eq)
  have hz : h≠z := fun eq=>(ne_of_lt k7)
    (clean_clock_inj_before_eight M k8 (by decide) M.firstClean M.cleanSeven eq)
  have xz : x≠z := fun eq=>(by decide : (6:Fin 10)≠7)
    (clean_clock_inj_before_eight M (by decide) (by decide) M.cleanSix M.cleanSeven eq)
  have h0 : h≠0 := M.firstClockNe
  have x0 : x≠0 := fun eq=>(by decide : (6:Fin 10)≠0)
    (clean_clock_inj_before_eight M (by decide) (by decide) M.cleanSix M.rankData.cleanZero
      (eq.trans M.rankData.clockZero.symm))
  have z0 : z≠0 := fun eq=>(by decide : (7:Fin 10)≠0)
    (clean_clock_inj_before_eight M (by decide) (by decide) M.cleanSeven M.rankData.cleanZero
      (eq.trans M.rankData.clockZero.symm))
  have h1 : h≠1 := fun eq=>k9 (M.rankData.uniqueOne k M.firstClean eq)
  have x1 : x≠1 := fun eq=>(by decide : (6:Fin 10)≠9) (M.rankData.uniqueOne 6 M.cleanSix eq)
  have z1 : z≠1 := fun eq=>(by decide : (7:Fin 10)≠9) (M.rankData.uniqueOne 7 M.cleanSeven eq)
  have hS : h∈S := Finset.mem_erase.mpr ⟨h0,Finset.mem_erase.mpr
    ⟨h1,mem_cleanKnots.mpr ⟨k,M.firstClean,rfl⟩⟩⟩
  have xS : x∈S := Finset.mem_erase.mpr ⟨x0,Finset.mem_erase.mpr
    ⟨x1,mem_cleanKnots.mpr ⟨6,M.cleanSix,rfl⟩⟩⟩
  have zS : z∈S := Finset.mem_erase.mpr ⟨z0,Finset.mem_erase.mpr
    ⟨z1,mem_cleanKnots.mpr ⟨7,M.cleanSeven,rfl⟩⟩⟩
  have ce : nodalHull S = (LobattoEight.lobattoCubic : K[X]) := marked_paid_clean_cubic ho M
  have root {u : K} (hu : u∈S) : lobattoNumer u=0 := by
    apply scalar_root_of_cubic ho
    rw [←ce]
    exact nodalHull_eval_of_mem hu
  refine ⟨⟨hx,hz,xz,root hS,root xS,root zS⟩,?_⟩
  have grid : S=({h,x,z}:Finset K) := by
    ext u
    constructor
    · intro hu
      obtain ⟨u0,hu'⟩ := Finset.mem_erase.mp hu
      obtain ⟨u1,hu''⟩ := Finset.mem_erase.mp hu'
      obtain ⟨j,gj,ju⟩ := mem_cleanKnots.mp hu''
      have vals := marked_clean_value_census M j gj
      rw [ju] at vals
      simp only [Finset.mem_insert,Finset.mem_singleton]
      rcases vals with eq|eq|eq|eq|eq
      · exact (u0 eq).elim
      · exact Or.inl eq
      · exact Or.inr (Or.inl eq)
      · exact Or.inr (Or.inr eq)
      · exact (u1 eq).elim
    · intro hu
      simp only [Finset.mem_insert,Finset.mem_singleton] at hu
      rcases hu with rfl|rfl|rfl
      · exact hS
      · exact xS
      · exact zS
  have hn : h∉({x,z}:Finset K) := by simp [hx,hz]
  have xn : x∉({z}:Finset K) := by simp [xz]
  have q : quartic h x z=(X:K[X])*nodalHull S := by
    rw [grid,nodalHull,Finset.prod_insert hn,Finset.prod_insert xn,Finset.prod_singleton]
    simp only [quartic,tapFactor,cleanPair]
    ring
  exact q.trans (congrArg (fun W : K[X]=>(X:K[X])*W) ce)

/-- The precise existing consumer record, earned from actual order and
Marked placement alone. No new geometric or terminal assumption. -/
theorem clean_primitive_placement_of_marked (ho : HasOrder 8 A b)
    (M : Placement A b P dup k) : CleanPrimitivePlacement A b k 6 (nodes A 7) := by
  obtain ⟨roots,quarticId⟩ := marked_actual_clean_geometry ho M
  refine ⟨M.rankData.cleanNine,M.rankData.clockNine,M.firstClean,M.cleanSix,
    ?_,?_,marked_clean_value_census M,?_,?_,le_of_eq M.rankData.treeFive,roots,quarticId⟩
  · intro j hj gj
    rw [M.noEarlierNonzeroClean j hj gj,M.rankData.clockZero]
  · intro j hj gj
    exact marked_clean_prefix_six M hj gj
  · change FourOffPhysical.cleanMass A b (nodes A k)≠0
    exact M.rankData.cleanMassNe _ (mem_cleanKnots.mpr ⟨k,M.firstClean,rfl⟩)
  · change FourOffPhysical.cleanMass A b (nodes A 6)≠0
    exact M.rankData.cleanMassNe _ (mem_cleanKnots.mpr ⟨6,M.cleanSix,rfl⟩)

/-- Literal strict Fin 10 order-eight four-off input, with no additional
rank, profile, clock-root, or distinctness hypothesis. -/
theorem paired_placements_of_order8_four_off
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b) (off : (offKnots A).card=4) :
    ∃ (P : K[X]) (dup k : Fin 10),
      Placement A b P dup k ∧ CleanPrimitivePlacement A b k 6 (nodes A 7) := by
  obtain ⟨P,dup,k,M⟩ := physical_placement_of_order8_four_off ha ho off
  exact ⟨P,dup,k,M,clean_primitive_placement_of_marked ho M⟩

end RKResearch.Certified.Graded.FourOffNewton
