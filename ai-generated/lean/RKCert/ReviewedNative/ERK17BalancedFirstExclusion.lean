module

public import RKCert.ReviewedNative.FirstSeedBalanced
public import RKCert.ReviewedNative.ERK17WideRank
public import RKCert.ReviewedNative.ERKUniform

@[expose] public section

/-! # Exclude the complete finite balanced-wide band at width twenty-six

Nine or ten original seed clocks are all that the paid rank-ten
annihilator can hold. Equilibrium coalescing plus the eight clean
receiver clocks rules out both widths. At nine clocks the alternative
with all output weights on seed rows is excluded by incoming Hermite. -/
namespace RKResearch.Certified.ERK17
open RKResearch Module Polynomial RKCert.Endpoint RKCert.Endpoint.WeightedClock
open RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse
open RKResearch.Certified.Graded.Reverse.FirstWide
open scoped Classical
noncomputable section

variable {K : Type*} [Field K]
set_option maxRecDepth 3500
set_option maxHeartbeats 900000

private theorem diag_ker_cap (d : Fin 26→K) :
    (Finset.univ.filter (fun i=>d i≠0)).card + finrank K ((diag d).ker) ≤ 26 := by
  let D := Finset.univ.filter (fun i=>d i≠0)
  let M : (diag d).range →ₗ[K] (D→K) :=
    (LinearMap.funLeft K K Subtype.val).comp (diag d).range.subtype
  have surj : Function.Surjective M := by
    intro h
    let w (i : Fin 26) : K := if hi : i∈D then h ⟨i,hi⟩/d i else 0
    refine ⟨⟨diag d w,⟨w,rfl⟩⟩,?_⟩
    funext i
    change d i.val * w i.val = h i
    have nz : d i.val≠0 := (Finset.mem_filter.mp i.property).2
    dsimp only [w]
    rw [dite_eq_left i.property,←mul_div_assoc,mul_div_cancel_left₀ _ nz]
  have r := LinearMap.finrank_le_finrank_of_surjective surj
  rw [Module.finrank_fintype_fun_eq_card,Fintype.card_coe] at r
  have rk := LinearMap.finrank_range_add_finrank_ker (diag d)
  rw [Module.finrank_fin_fun] at rk
  change D.card + finrank K ((diag d).ker) ≤ 26
  omega

private theorem balanced_kernel_cap_eight {c d : Fin 26→K}
    (balance : ∀ a,clockMass c d a=0)
    (nine : (weightedSites c d).card=9) : finrank K ((diag d).ker) ≤ 8 := by
  have both := balanced_support_double balance
  have rk := diag_ker_cap d
  omega

private theorem nonzero_active_count_eight {A : Matrix (Fin 26) (Fin 26) K}
    {b : Fin 26→K} (ho : HasOrder 17 A b) :
    8≤((activeClockSites (nodes A) b).erase 0).card := by
  have h := Finset.pred_card_le_card_erase (s:=activeClockSites (nodes A) b) (a:=0)
  have ck := live_aggregate_clock_count ho (q:=8) (by decide)
  omega

variable [LinearOrder K] [IsStrictOrderedRing K]
variable {A : Matrix (Fin 26) (Fin 26) K} {b : Fin 26→K}

private theorem impossible_all_output_on_nine_balanced_seed_sites
    (ha : ∀ i j,i ≤ j → A i j=0) (ho : HasOrder 17 A b)
    (W : WideLinear A b) (S : OddBalancedFrame A b 8 2)
    (balance : ∀ a,clockMass (nodes A) (firstSeed A b) a=0)
    (nine : (weightedSites (nodes A) (firstSeed A b)).card=9)
    (on : ∀ i,b i≠0 → firstSeed A b i≠0) : False := by
  let d := firstSeed A b
  let T := weightedSites (nodes A) d
  let V := (diag d).ker
  let B := W.firstCover
  have inc : activeClockSites (nodes A) b⊆T := by
    intro a aA
    obtain ⟨i,bi,e⟩ := mem_weightedSites.mp (activeClockSites_in_weightedSites _ _ aA)
    exact mem_weightedSites.mpr ⟨i,on i bi,e⟩
  have num : T.card ≤ (activeClockSites (nodes A) b).card := by
    change T.card=9 at nine
    rw [nine]
    exact live_aggregate_clock_count ho (q:=8) (by decide)
  have all : activeClockSites (nodes A) b=T := Finset.eq_of_subset_of_card_le inc num
  have sub : zeroSpace A 7 ≤ V := by
    intro v hv
    apply LinearMap.mem_ker.mpr
    ext i
    change d i * v i=0
    by_cases dz : d i=0
    · rw [dz,zero_mul]
    · have a : nodes A i∈T := mem_weightedSites.mpr ⟨i,dz,rfl⟩
      have ax : nodes A i∈activeClockSites (nodes A) b := all.symm ▸ a
      have live := clockMass_ne_of_active ax
      have trace (w : Fin 26→K) (hw : w∈zeroSpace A 7) : d*w∈originalCarrier A b :=
        B.original_represent (seed_times_tree_annih ho (j:=7) (q:=8) (by decide)
          (zeroSpace_le_treeSpace A 7 hw))
      have clean := B.clean_of_active_seed ho (j:=7) (by decide) balance trace i dz live (fun j _ h=>on j h)
      rw [clean v hv,mul_zero]
  have rk := balanced_kernel_cap_eight balance nine
  change finrank K V≤8 at rk
  have f7 := W.forward_seven ha ho S
  have same : zeroSpace A 7=V := by
    apply Submodule.eq_of_le_of_finrank_le sub
    change finrank K V ≤ finrank K (zeroSpace A 7)
    omega
  have inv : (zeroSpace A 7).map (diag (nodes A)) ≤ zeroSpace A 7 := by
    rw [same]
    rintro _ ⟨v,hv,rfl⟩
    apply LinearMap.mem_ker.mpr
    ext i
    have z : d i*v i=0 := congrFun (LinearMap.mem_ker.mp hv) i
    change d i*(nodes A i*v i)=0
    rw [show d i*(nodes A i*v i)=nodes A i*(d i*v i) by ring,z,mul_zero]
  have sep := (PolySeparated.of_coeff S.separated).mono (by decide : 7 ≤ 8)
  have q := clock_invariant_incoming ha (j:=6) sep inv
  change finrank K (zeroSpace A 6)+3 ≤ finrank K (zeroSpace A 7) at q
  have five := grade_five_surplus_of_reviewed_order ha ho (by decide)
  have six := zeroSpace_rank_interval_of_separation ha S.separated (j:=5) (d:=1)
    (by decide) (by decide)
  change finrank K (zeroSpace A 5)+1 ≤ finrank K (zeroSpace A 6) at six
  omega

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem clean_prefix_floor_eight {n : ℕ} {T : Matrix (Fin n) (Fin n) K} {w : Fin n→K}
    (ha : ∀ i j,i ≤ j → T i j=0) (ho : HasOrder 8 T w) : 10 ≤ n := by
  have f := erk_even_midpoint_floor ha ho (q:=4) (by decide) (by decide)
  omega

theorem width26_no_balanced_wide_first_seed
    (ha : ∀ i j,i ≤ j → A i j=0) (ho : HasOrder 17 A b)
    (W : WideLinear A b) (S : OddBalancedFrame A b 8 2)
    (balance : ∀ a,clockMass (nodes A) (firstSeed A b) a=0) : False := by
  classical
  let : DecidableEq K := Classical.decEq K
  let c := nodes A
  let d := firstSeed A b
  let T := weightedSites c d
  let B := W.firstCover
  have lo : 9 ≤ T.card := by
    have e := first_seed_site_card_eq (A:=A) (b:=b)
    have l := W.1
    change 9 ≤ (weightedSites (reflectedClock A) (firstSeed A b)).card at l
    change 9 ≤ (weightedSites (nodes A) (firstSeed A b)).card
    omega
  have cap : T.card ≤ 10 := by
    have h := Submodule.finrank_mono (B.balanced_carrier_le_annih ho (j:=7) (by decide) balance)
    rw [originalCarrier_rank,W.ann_seven_rank ha ho S] at h
    exact h
  have qCap := W.ann_seven_rank ha ho S
  have room : finrank K (annih (treeSpace A 7))=T.card ∨
      (finrank K (annih (treeSpace A 7))=T.card+1 ∧
       ∃ i,firstSeed A b i=0 ∧ b i≠0) := by
    by_cases ten : T.card=10
    · exact Or.inl (qCap.trans ten.symm)
    have nine : T.card=9 := by omega
    by_cases off : ∃ i,firstSeed A b i=0 ∧ b i≠0
    · exact Or.inr ⟨by omega,off⟩
    exact False.elim (impossible_all_output_on_nine_balanced_seed_sites ha ho W S balance nine
      (fun i iLive z => off ⟨i,z,iLive⟩))
  have trace (f : Fin 26→K) (hf : f∈zeroSpace A 8) : d*f∈originalCarrier A b :=
    B.balanced_middle_trace ho (j:=7) (by decide) (by decide) balance room hf
  have nonzero := nonzero_active_count_eight ho
  have one := (by decide : 1≤8).trans nonzero
  have cut := B.coalesced_clean_prefix_budget ho ha (j:=7) (by decide) balance
    (fun _ live => B.clean_at_active_clock ho (j:=8) (by decide) balance trace live) trace
    one 10 clean_prefix_floor_eight
  change 9≤(weightedSites (nodes A) (firstSeed A b)).card at lo
  omega

/-- Exact native nonzero first-seed dichotomy after the finite balanced
wide exclusion. The ≤ 2-site and ≥17-site branches remain separate. -/
theorem ordered_width26_first_seed_local_or_ge_seventeen
    (ha : ∀ i j,i ≤ j → A i j=0) (ho : HasOrder 17 A b) (nz : firstSeed A b≠0) :
    (weightedSites (reflectedClock A) (firstSeed A b)).card ≤ 2 ∨
    17 ≤ (weightedSites (reflectedClock A) (firstSeed A b)).card := by
  let S := (ordered_width26_full_frame ha ho).1
  rcases width26_linear_broad_or_local ha ho S nz with tiny|wide
  · exact Or.inl tiny
  right
  by_contra! small
  have eq := first_seed_site_card_eq (A:=A) (b:=b)
  exact width26_no_balanced_wide_first_seed ha ho wide S
    (first_seed_clockMass_zero ho (by omega))

end
end RKResearch.Certified.ERK17
