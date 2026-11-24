module

public import RKCert.ReviewedNative.ERKOrder16PaidFrame
public import RKCert.ReviewedNative.ReverseUnitQuadratic
public import RKCert.ReviewedNative.ReversePaidTraces
public import RKCert.ReviewedNative.ClockHeadFibers

@[expose] public section

/-! # Six true quadratic reverse powers at width 24

The no-single-site theorem and the actual unit flag exclude small
supports; the sixth outgoing Hermite gain is compared with the
original E7 annihilator. Seven distinct sites already suffice for the
degree-refund and chronological ports. No scalar arithmetic is used. -/
namespace RKResearch.Certified.ERK16

open RKResearch Module Polynomial RKCert.Endpoint RKCert.Endpoint.WeightedClock
open RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse
open scoped Classical Matrix

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A : Matrix (Fin 24) (Fin 24) K} {b : Fin 24 → K}

structure Width24QuadraticCover (A : Matrix (Fin 24) (Fin 24) K) (b : Fin 24 → K) : Prop where
  frame : Width24PaidFrame A b
  sites : 7≤(weightedSites (reflectedClock A) (quadraticSeed A b)).card
  band : annih (treeSpace A 8) = weightedBand (reflectedClock A) (quadraticSeed A b) 6
  lastSeed : quadraticSeed A b (Fin.last 23)=0

/-- The entire actual E8 annihilator is the band of the first six
quadratic seed powers, with a strict surplus in the number of clock
sites. -/
theorem width24_quadratic_cover_of_frame (ha : ∀ i j,i≤j → A i j=0)
    (ho : HasOrder 16 A b) (F : Width24PaidFrame A b) : Width24QuadraticCover A b := by
  let y := reflectedClock A
  let d := quadraticSeed A b
  let c := (weightedSites y d).card
  let L := primitiveBack A b
  have start : d∈L 1 := adjointFlag_credit (monomialCredit A b) 0 (monomial_mem_credit 0 1 (by decide))
  have inc (n : ℕ) (hn : 1≤n) : weightedBand y d n≤L n := by
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
    simpa only [Nat.add_comm 1 k] using (weighted_band_of_primitive_seed start k)
  have ranks (n : ℕ) (hn : n≤6) : finrank K (L n)=n := by
    obtain ⟨r,e⟩ := F.flagExact n hn
    change back A b n=L n at e
    rw [←e,r]
  have escape (n : ℕ) (lo : 2≤n) (hi : n≤5) : ¬(L n).map (diag y)≤L n := by
    intro h
    have jump := reverse_clock_invariant_gain ha ho n (by omega) h
    change finrank K (L n)+(n+2)/2≤finrank K (L (n+1)) at jump
    rw [ranks n (by omega),ranks (n+1) (by omega)] at jump
    omega
  have unit : UnitQuadratic.UnitFrame A b :=
    ⟨F.seedZero,fun n hn=>F.flagExact n (by omega),fun n lo hi=>escape n lo (by omega)⟩
  have two : 2≤c := UnitQuadratic.quadratic_sites_ge_two ha ho (by decide) unit
  have middle_noninv : ¬(L 6).map (diag y)≤L 6 := by
    intro inv
    have gain := reverse_clock_invariant_gain ha ho 6 (by decide) inv
    change finrank K (L 6)+(6+2)/2≤finrank K (L 7) at gain
    rw [ranks 6 (by decide)] at gain
    have up := Submodule.finrank_mono (primitiveBack_annih ho 7 7 (by decide))
    have r5 := grade_five_surplus_of_reviewed_order ha ho (by decide)
    have sep := coeff_separated ho (q:=7) (by decide)
    have strict5 := Submodule.finrank_lt_finrank_of_lt
      (zeroSpace_strict_of_separation ha (j:=5) sep (by decide) (by decide))
    have strict6 := Submodule.finrank_lt_finrank_of_lt
      (zeroSpace_strict_of_separation ha (j:=6) sep (by decide) (by decide))
    change finrank K (zeroSpace A 5)<finrank K (zeroSpace A 6) at strict5
    change finrank K (zeroSpace A 6)<finrank K (zeroSpace A 7) at strict6
    have e7 := erk_midpoint_tree_rank ha ho (q:=7) (by decide) (by decide)
    have an := finrank_annih (treeSpace A 7)
    rw [Fintype.card_fin,e7] at an
    change finrank K (L 7)≤finrank K (annih (treeSpace A 7)) at up
    omega
  have seven : 7≤c := by
    by_contra! few
    have eq : weightedBand y d c=L c := by
      apply Submodule.eq_of_le_of_finrank_le (inc c (by omega))
      rw [ranks c (by omega),weightedBand_rank y d c le_rfl]
    have sat : L c = (weightedEval y d).range :=
      eq.symm.trans (weightedBand_eq_range y d c le_rfl)
    have stable : (L c).map (diag y)≤L c := by
      rintro _ ⟨v,hv,rfl⟩
      rw [sat] at hv ⊢
      exact weighted_range_clock y d hv
    by_cases last:c=6
    · rw [last] at stable
      exact middle_noninv stable
    · exact escape c two (by omega) stable
  have wb : weightedBand y d 6=L 6 := by
    apply Submodule.eq_of_le_of_finrank_le (inc 6 (by decide))
    rw [ranks 6 (by decide),weightedBand_rank y d 6 (show 6≤c by omega)]
  have last := (mem_tailZero.mp (F.lastLive.seed_tail ha F.seedZero 1)) (Fin.last 23) le_rfl
  exact ⟨F,seven,F.full.symm.trans wb.symm,last⟩

theorem width24_quadratic_cover (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 16 A b) :
    Width24QuadraticCover A b := width24_quadratic_cover_of_frame ha ho (width24_paid_frame ha ho)

omit [IsStrictOrderedRing K] in
/-- Every true terminal-deleted complementary row has a degree-five
description on the same quadratic seed. -/
theorem Width24QuadraticCover.poly_cover (C : Width24QuadraticCover A b)
    {v : Fin 24 → K} (h : v∈zeroAt (annih (treeSpace A 8)) (Fin.last 23)) :
    ∃ P : K[X], P.natDegree≤5 ∧ weightedEval (reflectedClock A) (quadraticSeed A b) P=v := by
  have mem := (mem_zeroAt.mp h).1
  rw [C.band] at mem
  obtain ⟨P,d,e⟩ := mem_weightedBand.mp mem
  refine ⟨P,?_,e⟩
  by_cases z:P=0
  · simp [z]
  · have dp : P.natDegree<6 := (natDegree_lt_iff_degree_lt z).mpr d
    omega

omit [IsStrictOrderedRing K] in
theorem Width24QuadraticCover.supports (C : Width24QuadraticCover A b) :
    Thin.SupportsComplement A b 8 (Fin.last 23) :=
  Thin.supportsComplement_of_cover (h:=5) (fun _ h=>C.poly_cover h)

omit [IsStrictOrderedRing K] in
/-- A native pair of cheap ordinary grade-five powers automatically
refunds the trace degrees to the exact weak-four bounds 4 and 3. -/
theorem Width24QuadraticCover.two_power_traces (C : Width24QuadraticCover A b)
    (ho : HasOrder 16 A b) {f : Fin 24 → K}
    (f0 : f∈zeroSpace A 5) (f1 : diag (nodes A) f∈zeroSpace A 5) :
    ∃ Q P : K[X], Q.natDegree≤4 ∧ P.natDegree≤3 ∧
      (∀i,quadraticSeed A b i*f i=Q.eval (reflectedClock A i)*quadraticSeed A b i) ∧
      (∀i,reflectedClock A i*b i*f i=P.eval (reflectedClock A i)*quadraticSeed A b i) := by
  let D := diag (nodes A)
  have yz : reflectedClock A (Fin.last 23)=0 := by
    change 1-nodes A (Fin.last 23)=0
    rw [C.frame.lastClock,sub_self]
  have each (k : ℕ) (hk : k≤1) : (D^k) f∈zeroSpace A 5 := by
    rcases Nat.eq_zero_or_pos k with e|h
    · simpa [e] using f0
    · have e : k=1 := by omega
      simpa [e,D] using f1
  exact Thin.thin_reverse_traces_same_grade_drop ho (j:=5) (h:=5) (m:=8)
    (by decide) (by decide) (by decide) (Fin.last 23) yz C.lastSeed (by exact C.sites)
    (fun _ h=>C.poly_cover h) (k:=1) (fun k => (D^k) f) each
    (fun k _ i _ => HeadFiber.clock_power_value _ _ _ _)

end
end RKResearch.Certified.ERK16
