module

public import RKCert.ReviewedNative.BalancedSeedRepresentatives

@[expose] public section

/-! # Genuine exclusion of the balanced wide first-adjoint branch

This only addresses the nonzero first seed. Every kept clock class
has an earliest physical row; the necessary derivative features
through tree order nine agree at every omitted row. -/
namespace RKResearch.Certified.ERK19
open RKResearch Module Polynomial Graded Graded.Reverse RKCert.Endpoint RKCert.Endpoint.WeightedClock
open scoped Classical Matrix
noncomputable section
variable {K : Type*} [Field K]

private theorem diag_ker_cap (d : Fin 29→K) :
    (Finset.univ.filter (fun i=>d i≠0)).card + finrank K ((diag d).ker) ≤ 29 := by
  let D := Finset.univ.filter (fun i=>d i≠0)
  let M : (diag d).range →ₗ[K] (D→K) :=
    (LinearMap.funLeft K K Subtype.val).comp (diag d).range.subtype
  have surj : Function.Surjective M := by
    intro h
    let w (i : Fin 29) : K := if hi : i∈D then h ⟨i,hi⟩/d i else 0
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
  change D.card + finrank K ((diag d).ker) ≤ 29
  omega

variable [LinearOrder K] [IsStrictOrderedRing K]
variable {A : Matrix (Fin 29) (Fin 29) K} {b : Fin 29→K}

set_option maxHeartbeats 300000 in
private theorem impossible_all_output_on_ten_balanced_seed_sites
    (ha : ∀ i j,i ≤ j → A i j=0) (ho : HasOrder 19 A b)
    (band : FullFirstBand A b) (balance : ∀ a,clockMass (nodes A) (firstSeed A b) a=0)
    (ten : (weightedSites (nodes A) (firstSeed A b)).card=10)
    (on : ∀ i,b i≠0 → firstSeed A b i≠0) : False := by
  let d := firstSeed A b
  let T := weightedSites (nodes A) d
  let V := (diag d).ker
  have inc : activeClockSites (nodes A) b ⊆ T := by
    intro a aA
    obtain ⟨i,bi,e⟩ := mem_weightedSites.mp (activeClockSites_in_weightedSites _ _ aA)
    exact mem_weightedSites.mpr ⟨i,on i bi,e⟩
  have aCard : T.card ≤ (activeClockSites (nodes A) b).card := by
    rw [show T.card=10 from ten]
    exact order19_active_clock_count ho
  have all : activeClockSites (nodes A) b = T := Finset.eq_of_subset_of_card_le inc aCard
  have sub : zeroSpace A 8  ≤  V := by
    intro f hf
    apply LinearMap.mem_ker.mpr
    ext i
    change d i * f i = 0
    by_cases z : d i=0
    · rw [z,zero_mul]
    · have a : nodes A i∈T := mem_weightedSites.mpr ⟨i,z,rfl⟩
      have ax : nodes A i∈activeClockSites (nodes A) b := all.symm ▸ a
      have live : clockMass (nodes A) b (nodes A i)≠0 := clockMass_ne_of_active ax
      have trace (w : Fin 29→K) (hw : w∈zeroSpace A 8) :
          d*w∈OriginalFirstCarrier A b :=
        band.represent (first_seed_mixed_annih ho (j:=8) (k:=9) (by decide) (zeroSpace_le_treeSpace A 8 hw))
      have clean := clean_of_active_seed_clock ho (q:=8) (by decide) band balance trace i z live
        (fun j _ bj=>on j bj)
      rw [clean f hf,mul_zero]
  have both := balanced_support_double balance
  change 2*T.card ≤ _ at both
  have rk := diag_ker_cap (firstSeed A b)
  change T.card = 10 at ten
  have f8 := (width29_eight_nine ha ho).1
  have eq : zeroSpace A 8 = V := by
    apply Submodule.eq_of_le_of_finrank_le sub
    change finrank K ((diag (firstSeed A b)).ker) ≤ finrank K (zeroSpace A 8)
    omega
  have inv : (zeroSpace A 8).map (diag (nodes A))  ≤  zeroSpace A 8 := by
    rw [eq]
    rintro _ ⟨f,hf,rfl⟩
    apply LinearMap.mem_ker.mpr
    ext i
    have z : d i*f i=0 := congrFun (LinearMap.mem_ker.mp hf) i
    change d i*(nodes A i*f i)=0
    calc
      _ = nodes A i*(d i*f i) := by ring
      _ = 0 := by rw [z,mul_zero]
  have sep : PolySeparated A 8 :=
    PolySeparated.of_coeff (coeff_separated ho (by decide))
  have g := clock_invariant_incoming ha (j:=7) sep inv
  have l := zeroSpace_finrank ha ho (n:=6) (by decide)
  change finrank K (zeroSpace A 7)+4  ≤  finrank K (zeroSpace A 8) at g
  change 6  ≤  finrank K (zeroSpace A 7) at l
  omega

set_option maxHeartbeats 1200000 in
private theorem impossible_balanced_seed_with_clean_receivers
    (ha : ∀ i j,i ≤ j → A i j=0) (ho : HasOrder 19 A b) (band : FullFirstBand A b)
    (balance : ∀ a,clockMass (nodes A) (firstSeed A b) a=0)
    (wide : 10 ≤ (weightedSites (nodes A) (firstSeed A b)).card)
    (split : (weightedSites (nodes A) (firstSeed A b)).card=11 ∨
      ((weightedSites (nodes A) (firstSeed A b)).card=10 ∧
       ∃i, firstSeed A b i=0 ∧ b i≠0)) : False := by
  let c := nodes A
  let d := firstSeed A b
  let R := seedRepresentatives c d
  let n := R.card
  let E := R.orderIsoOfFin (rfl : R.card=n)
  let e : Fin n→Fin 29 := fun j=>(E j).val
  let r (i : Fin 29) : Fin n :=
    E.symm ⟨seedRep c d i, Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩
  have es (i : Fin 29) : e (r i)=seedRep c d i := by
    dsimp only [e,r]
    rw [E.apply_symm_apply]
  have order : Monotone e := fun _ _ h => E.monotone h
  have earlier (i : Fin 29) : e (r i) ≤ i := (es i).symm ▸ seedRep_le c d i
  have agree (v : Fin 29→K) (hv : v∈treeSpace A 8) (i : Fin 29) : v (e (r i))=v i := by
    rw [es]
    by_cases z : d i=0
    · rw [seedRep_of_dead z]
    · have p := seedRep_live (c:=c) z
      exact first_seed_fibre_tree_eight ho band hv p.1 z p.2
  let B := causalMergeMatrix A e r
  have strict := causalMerge_strict ha order earlier
  let T := (activeClockSites (nodes A) b).erase 0
  let L := Finset.univ.filter (fun i : Fin n =>
    nodes B i≠0 ∧ ∀ v∈zeroSpace B 9, v i=0)
  have covers : T ⊆ L.image (nodes B) := by
    intro a aT
    have a0 := (Finset.mem_erase.mp aT).1
    have ax := (Finset.mem_erase.mp aT).2
    obtain ⟨i,ci,cl⟩ := balanced_active_has_clean_nine ha ho band balance split ax
    have atRep : nodes A (e (r i))=a ∧ ∀ f∈zeroSpace A 9, f (e (r i))=0 := by
      rw [es]
      by_cases z : d i=0
      · rw [seedRep_of_dead z]
        exact ⟨ci,cl⟩
      · have rp := seedRep_live (c:=c) z
        refine ⟨rp.2.trans ci,fun f hf=>?_⟩
        have cf := balanced_grade_nine_first_trace ha ho band balance split hf
        exact (first_carrier_fibre_agreement cf rp.1 z rp.2).trans (cl f hf)
    obtain ⟨clock,clean⟩ := clean_causalMerge agree (r i) atRep.2
    exact Finset.mem_image.mpr
      ⟨r i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,(clock.trans atRep.1).symm ▸ a0,clean⟩,
        clock.trans atRep.1⟩
  have t9 : 9 ≤ T.card := by
    have h := Finset.pred_card_le_card_erase (s:=activeClockSites (nodes A) b) (a:=0)
    have g := order19_active_clock_count ho
    change (activeClockSites (nodes A) b).card - 1  ≤  T.card at h
    omega
  have many : 9 ≤ L.card := t9.trans
    ((Finset.card_le_card covers).trans Finset.card_image_le)
  let j := L.min' (Finset.card_pos.mp (by omega : 0<L.card))
  have jm : j∈L := Finset.min'_mem _ _
  have hClean : nodes B j≠0 ∧ ∀ w∈zeroSpace B 9, w j=0 := (Finset.mem_filter.mp jm).2
  have H := exact_receiver_prefix_order strict j 9 hClean.1 hClean.2
  have low : 12 ≤ j.val := by
    have ha' (i k : Fin j.val) (h : i ≤ k) :
        ((nodes B j)⁻¹ • prefixMatrix B j.isLt.le) i k=0 := by
      rw [Matrix.smul_apply,prefix_strict_lower strict j.isLt.le i k h,smul_zero]
    exact odd_midpoint_floor ha' H (q:=4) (by decide) (by decide)
  let f (i : L) : Fin (n-j.val) := ⟨i.val.val-j.val,by
    have le := Finset.min'_le _ _ i.property
    have := i.val.isLt
    change j.val ≤ i.val.val at le
    omega⟩
  have inj : Function.Injective f := by
    intro u v equal
    apply Subtype.ext
    apply Fin.ext
    have eu := congrArg Fin.val equal
    change u.val.val-j.val = v.val.val-j.val at eu
    have z1 := Finset.min'_le _ _ u.property
    have z2 := Finset.min'_le _ _ v.property
    change j.val  ≤  u.val.val at z1
    change j.val  ≤  v.val.val at z2
    omega
  have lcap : L.card ≤ n-j.val := by
    have fcap := Fintype.card_le_of_injective f inj
    simpa only [Fintype.card_fin,Fintype.card_coe] using fcap
  have compressed := balanced_seed_representative_count balance
  change n+(weightedSites c d).card ≤ 29 at compressed
  change 10 ≤ (weightedSites c d).card at wide
  omega

/-- Closing the balanced wide branch uses only exact reviewed order,
strictness, and the full first-seed band that the wide support pays.
The first remaining wide support must have nonzero clock aggregates. -/
theorem width29_no_balanced_wide_first_seed
    (ha : ∀ i j,i ≤ j → A i j=0) (ho : HasOrder 19 A b)
    (wide : 10 ≤ (weightedSites (nodes A) (firstSeed A b)).card)
    (band : FullFirstBand A b) (balance : ∀ a,clockMass (nodes A) (firstSeed A b) a=0) : False := by
  have cap := Submodule.finrank_mono (balanced_first_carrier_le_annih_eight ho band balance)
  rw [first_carrier_rank,width29_annih_eight_rank ha ho] at cap
  by_cases h : (weightedSites (nodes A) (firstSeed A b)).card=11
  · exact impossible_balanced_seed_with_clean_receivers ha ho band balance wide (Or.inl h)
  have ten : (weightedSites (nodes A) (firstSeed A b)).card=10 := by omega
  by_cases out : ∃i, firstSeed A b i=0 ∧ b i≠0
  · exact impossible_balanced_seed_with_clean_receivers ha ho band balance wide (Or.inr ⟨ten,out⟩)
  exact impossible_all_output_on_ten_balanced_seed_sites ha ho band balance ten
    (fun i live h => out ⟨i,h,live⟩)

/-- Every genuine width-29 nonzero first seed is either on at most two
clocks, or on at least nineteen. All balanced wide clocks are excluded. -/
theorem width29_first_seed_local_or_ge_nineteen
    (ha : ∀ i j,i ≤ j → A i j=0) (ho : HasOrder 19 A b) (nz : firstSeed A b≠0) :
    (weightedSites (reflectedClock A) (firstSeed A b)).card ≤ 2 ∨
    19 ≤ (weightedSites (reflectedClock A) (firstSeed A b)).card := by
  rcases width29_nonzero_broad_or_local ha ho nz with h | ⟨h,band⟩
  · exact Or.inl h
  right
  by_contra! small
  have eq := first_seed_site_card_eq (A:=A) (b:=b)
  exact width29_no_balanced_wide_first_seed ha ho (by omega) band
    (first_seed_clockMass_zero ho (by omega))

end
end RKResearch.Certified.ERK19
