module

public import RKCert.ReviewedNative.ERK19EndpointFrontier
public import RKCert.ReviewedNative.ERK17ReverseSupport
public import RKCert.ReviewedNative.ReverseUnitQuadratic

@[expose] public section

/-! # The actual order-19 reverse support, including the localized quadratic case

At width 29 the full grade-eight annihilator has only eleven
dimensions. Even with a zero first seed it cannot pay the five
directions that an invariant last reverse clock band would cost. -/
namespace RKResearch.Certified.ERK19
open RKResearch Module Polynomial Graded Graded.Reverse RKCert.Endpoint RKCert.Endpoint.WeightedClock
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A : Matrix (Fin 29) (Fin 29) K} {b : Fin 29→K}
noncomputable section

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem reverse_rank (F : OddBalancedFrame A b 9 2) {n : ℕ} (hi : n≤8) :
    finrank K (primitiveBack A b n)=n+finrank K (back A b 0) := by
  obtain ⟨r,e⟩ := F.reverse.flagExact n hi
  rwa [←e]

/-- Reflected-clock invariance fails at every charged reverse grade,
including the last one, independently of the first-seed branch. -/
theorem width29_reverse_clock_escape (ha : ∀ i k, i≤k → A i k=0) (ho : HasOrder 19 A b)
    {n : ℕ} (lo : 2≤n) (hi : n≤8) :
    ¬ (primitiveBack A b n).map (diag (reflectedClock A)) ≤ primitiveBack A b n := by
  intro inv
  have F := (ordered_width29_frame ha ho).1
  have gain := reverse_clock_invariant_gain ha ho n (by omega) inv
  rw [reverse_rank F hi] at gain
  by_cases last : n=8
  · subst n
    have f := (width29_eight_nine ha ho).1
    have t := treeSpace_rank_eq_of_separation ho (q:=8) (by decide) (coeff_separated ho (by decide))
    have d := finrank_annih (treeSpace A 8)
    rw [Fintype.card_fin] at d
    have m := Submodule.finrank_mono (primitiveBack_annih ho 8 9 (by decide))
    change 8+finrank K (back A b 0)+5 ≤ finrank K (primitiveBack A b 9) at gain
    omega
  · rw [reverse_rank F (show n+1≤8 by omega)] at gain
    omega

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem invariant_of_full_weighted {y v : Fin 29→K} {U : Submodule K (Fin 29→K)}
    (eq : U=(weightedEval y v).range) : U.map (diag y) ≤ U := by
  rintro _ ⟨w,hw,rfl⟩
  rw [eq] at hw ⊢
  exact weighted_range_clock y v hw

/-- If the first genuine weighted adjoint seed vanishes, the second
seed spans the full terminal-zero annihilator via its first eight
clock powers; its support uses at least nine distinct physical clocks. -/
theorem width29_zero_quadratic_cover (ha : ∀ i k, i≤k → A i k=0) (ho : HasOrder 19 A b)
    (z : firstSeed A b=0) :
    9≤(weightedSites (reflectedClock A) (quadraticSeed A b)).card ∧
    zeroAt (annih (treeSpace A 9)) (Fin.last 28)=
      weightedBand (reflectedClock A) (quadraticSeed A b) 8 := by
  let d := quadraticSeed A b
  let y := reflectedClock A
  let c := (weightedSites y d).card
  let L := primitiveBack A b
  have F := (ordered_width29_frame ha ho).1
  have short : UnitQuadratic.UnitFrame A b := by
    refine ⟨z,?_,fun n lo hi => width29_reverse_clock_escape ha ho lo (by omega)⟩
    intro n hn
    obtain ⟨r,e⟩ := F.reverse.flagExact n (by omega)
    rw [first_dim_zero z,add_zero] at r
    exact ⟨r,e⟩
  have two : 2≤c := UnitQuadratic.quadratic_sites_ge_two ha ho (by decide) short
  have rank (n : ℕ) (hn : n≤8) : finrank K (L n)=n := by
    have r := reverse_rank F hn
    rwa [first_dim_zero z,add_zero] at r
  have dm : d ∈ L 1 := adjointFlag_credit (monomialCredit A b) 0 (monomial_mem_credit 0 1 (by decide))
  have inc (n : ℕ) (hn : 1≤n) : weightedBand y d n ≤ L n := by
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
    simpa only [Nat.add_comm 1 k] using (weighted_band_of_primitive_seed dm k)
  have big : 9≤c := by
    by_contra! h
    have e : weightedBand y d c=L c := by
      apply Submodule.eq_of_le_of_finrank_le (inc c (by omega))
      rw [rank c (by omega),weightedBand_rank y d _ le_rfl]
    have full : L c=(weightedEval y d).range := e.symm.trans (weightedBand_eq_range y d _ le_rfl)
    exact width29_reverse_clock_escape ha ho two (by omega) (invariant_of_full_weighted full)
  have eql : weightedBand y d 8=L 8 := by
    apply Submodule.eq_of_le_of_finrank_le (inc 8 (by decide))
    rw [rank 8 (by decide),weightedBand_rank y d _ (show 8≤c by omega)]
  have final := (width29_zero_terminal ha ho z).2.2.2.2
  exact ⟨big,final.symm.trans eql.symm⟩

/-- The other branch is either genuinely localized at at most two
clocks, or the entire grade-nine annihilator is exactly the weighted
polynomial band of the first seed on at least ten clocks. -/
theorem width29_nonzero_broad_or_local (ha : ∀ i k, i≤k → A i k=0) (ho : HasOrder 19 A b)
    (nz : firstSeed A b≠0) :
    (weightedSites (reflectedClock A) (firstSeed A b)).card≤2 ∨
      (10≤(weightedSites (reflectedClock A) (firstSeed A b)).card ∧
       annih (treeSpace A 9)=weightedBand (reflectedClock A) (firstSeed A b) 9) := by
  let d := firstSeed A b
  let y := reflectedClock A
  let c := (weightedSites y d).card
  let L := primitiveBack A b
  have F := (ordered_width29_frame ha ho).1
  have dm : d∈L 0 := Submodule.mem_span_singleton_self d
  have inc (n : ℕ) : weightedBand y d (n+1) ≤ L n := by
    simpa only [Nat.zero_add] using (weighted_band_of_primitive_seed dm n)
  have rank (n : ℕ) (hn : n≤8) : finrank K (L n)=n+1 := by
    have r := reverse_rank F hn
    rwa [first_dim_one nz] at r
  change c≤2 ∨ _
  by_cases small : c≤2
  · exact Or.inl small
  right
  have big : 10≤c := by
    by_contra! h
    let n := c-1
    have e : n+1=c := by dsimp [n]; omega
    have hi : n≤8 := by dsimp [n]; omega
    have lo : 2≤n := by dsimp [n]; omega
    have eq : weightedBand y d (n+1)=L n := by
      apply Submodule.eq_of_le_of_finrank_le (inc n)
      rw [rank n hi,weightedBand_rank y d _ e.le]
    have full : L n=(weightedEval y d).range := eq.symm.trans (weightedBand_eq_range y d _ e.ge)
    exact width29_reverse_clock_escape ha ho lo hi (invariant_of_full_weighted full)
  have eq : weightedBand y d 9=L 8 := by
    apply Submodule.eq_of_le_of_finrank_le (inc 8)
    rw [rank 8 (by decide),weightedBand_rank y d _ (show 9≤c by omega)]
  have final : L 8=annih (treeSpace A 9) :=
    (F.reverse.flagExact 8 (by decide)).2.symm.trans (F.reverse.firstNonzero nz)
  exact ⟨big,final.symm.trans eq.symm⟩

end
end RKResearch.Certified.ERK19
