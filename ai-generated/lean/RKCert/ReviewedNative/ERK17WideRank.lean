module

public import RKCert.ReviewedNative.FirstSeedWideCarrier
public import RKCert.ReviewedNative.ERK17HiddenRank
public import RKCert.ReviewedNative.FiveHiddenHead

@[expose] public section

/-! # The genuine F7 surplus in the full first-seed case at width 26 -/
namespace RKResearch.Certified.ERK17
open RKResearch Module Polynomial RKCert.Endpoint RKCert.Endpoint.WeightedClock
open RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse
open RKResearch.Certified.Graded.Reverse.FirstWide
open RKCert.OneEscape
open scoped Classical
noncomputable section

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A : Matrix (Fin 26) (Fin 26) K} {b : Fin 26→K}
set_option maxRecDepth 3500
set_option maxHeartbeats 950000

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem WideLinear.firstCover (B : WideLinear A b) : FirstWide.Cover A b 8 7 :=
  FirstWide.Cover.of_band B.1 B.2

theorem WideLinear.no_four_carrier (B : WideLinear A b)
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 17 A b)
    (F : OddBalancedFrame A b 8 2) (dim : finrank K (FirstWide.carrier A b)=4) : False := by
  let H := FirstWide.carrier A b
  let V := FirstWide.visible A b
  let c := nodes A
  let y := reflectedClock A
  let d := firstSeed A b
  let cov := B.firstCover
  have stable : H.map (diag c)≤H := carrier_clock
  have toEight : H≤zeroSpace A 8 := cov.carrier_pure ho (by decide)
  have cap : finrank K (zeroSpace A 9)≤11 := by
    have b := F.nextRoom
    change finrank K (zeroSpace A 9)+_≤11 at b
    omega
  have hb (v : Fin 26→K) (hv : v∈H) (i : Fin 26) (hi : V i) : v i=0 :=
    mem_carrier_iff.mp hv i hi
  have detect (v : Fin 26→K) (_ : v∈zeroSpace A 8) (hi : ∀i,V i→v i=0) : v∈H :=
    mem_carrier_iff.mpr hi
  refine four_hidden_rank_dispatch ha (by decide) F.separated F.middleDefects cap
    H toEight dim stable V hb detect ?_ ?_
  · rintro f hf ⟨a,whereAt⟩
    obtain ⟨Q,P,qd,pd,fit⟩ := two_traces ho cov hf (by decide) (by decide) (by decide)
    let T := (weightedSites y d).erase (1-a)
    have sites : 8<(weightedSites y d).card := cov.sites
    have enough : 8≤T.card := by
      have e := Finset.pred_card_le_card_erase (s:=weightedSites y d) (a:=1-a)
      change (weightedSites y d).card-1≤T.card at e
      omega
    have qz : Q=0 := by
      apply eq_of_degrees_lt_of_eval_finset_eq T
      · exact degree_le_natDegree.trans_lt (by exact_mod_cast (show Q.natDegree<T.card by omega))
      · exact degree_le_natDegree.trans_lt (by
          rw [natDegree_zero]
          exact_mod_cast (show 0<T.card by omega))
      intro x hx
      obtain ⟨nx,inT⟩ := Finset.mem_erase.mp hx
      obtain ⟨i,dz,rfl⟩ := mem_weightedSites.mp inT
      have off : c i≠a := fun z => nx (by change 1-c i=1-a; rw [z])
      have q := fit.1 i
      rw [whereAt i (Or.inl dz) off,mul_zero] at q
      rw [eval_zero]
      exact (mul_eq_zero.mp q.symm).resolve_right dz
    exact mem_carrier_iff.mpr (fit_invisible fit qz)
  · intro j small w powers
    have j5 : 5≤j := by rcases small with z|z <;> omega
    have j6 : j≤6 := by rcases small with z|z <;> omega
    have reps (a : ℕ) (al : a≤j-4) : ∃ f : Fin 26→K, f∈zeroSpace A j ∧
        ∀ i, V i → f i=c i^a*w i := by
      obtain ⟨f,hf,u,hu,e⟩ := Submodule.mem_sup.mp (powers a (by omega))
      refine ⟨f,hf,fun i hi => ?_⟩
      have z := congrFun e i
      rw [Pi.add_apply,hb _ hu _ hi,add_zero,HeadFiber.clock_power_value] at z
      exact z
    let fam (a : ℕ) : Fin 26→K := if h:a≤j-4 then Classical.choose (reps a h) else 0
    have traces (a : ℕ) (h : a≤j-4) : fam a∈zeroSpace A j ∧
        ∀ i, V i → fam a i=c i^a*w i := by
      rw [show fam a=Classical.choose (reps a h) from dite_eq_left h]
      exact Classical.choose_spec (reps a h)
    obtain ⟨Q,P,qd,pd,fit⟩ := traces_same_grade_drop (f:=w) ho cov (by omega) (by omega)
      (by decide) (k:=j-4) fam (fun a ha=>(traces a ha).1) (fun a ha i hi => (traces a ha).2 i hi)
    have van := ordered_invisible_given_reps ha ho cov Q P (by omega) (by omega)
      (by omega) (by omega) (by omega) fit
    apply mem_carrier_iff.mpr
    intro i vi
    rcases vi with dz|bz
    · exact (mul_eq_zero.mp (van i).1).resolve_left dz
    · exact (mul_eq_zero.mp (van i).2).resolve_left bz

theorem WideLinear.carrier_rank_five (B : WideLinear A b)
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 17 A b)
    (S : OddBalancedFrame A b 8 2) :
    finrank K (FirstWide.carrier A b)=5 := by
  let H := FirstWide.carrier A b
  have h4 : zeroSpace A 4≤H := B.firstCover.grade_four_in_carrier ha ho (by decide)
    (by decide) (by decide) (by decide)
  have h8 : H≤zeroSpace A 8 := B.firstCover.carrier_pure ho (by decide)
  have stable : H.map (diag (nodes A))≤H := carrier_clock
  have cap : finrank K (zeroSpace A 9)≤11 := by
    have d := S.nextRoom
    change finrank K (zeroSpace A 9)+_≤11 at d
    omega
  have hhi : finrank K H≤5 := invariant_core_cap_of_rank ha (by decide) S.separated
    S.middleDefects cap H h8 stable
  have hlo : 4≤finrank K H := by
    have e3 := zeroSpace_rank_interval_of_separation ha S.separated (j:=1) (d:=2)
      (by decide) (by decide)
    have e4 := zeroSpace_rank_interval_of_separation ha S.separated (j:=1) (d:=3)
      (by decide) (by decide)
    change _+2≤finrank K (zeroSpace A 3) at e3
    change _+3≤finrank K (zeroSpace A 4) at e4
    have sm := Submodule.finrank_mono h4
    by_contra! tiny
    have E : zeroSpace A 4=H :=
      Submodule.eq_of_le_of_finrank_le h4 (by omega)
    have inv : (zeroSpace A 4).map (diag (nodes A))≤zeroSpace A 4 := E.symm ▸ stable
    have d := clock_invariant_incoming ha (j:=3)
      ((PolySeparated.of_coeff S.separated).mono (by decide : 4≤8)) inv
    change finrank K (zeroSpace A 3)+2≤finrank K (zeroSpace A 4) at d
    omega
  change finrank K H=5
  by_contra! z
  exact B.no_four_carrier ha ho S (by change finrank K H=4; omega)

theorem WideLinear.forward_seven (B : WideLinear A b)
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 17 A b)
    (S : OddBalancedFrame A b 8 2) : finrank K (zeroSpace A 7)=8 := by
  let H := FirstWide.carrier A b
  let C := diag (nodes A)
  have dim : finrank K H=5 := B.carrier_rank_five ha ho S
  have h8 : H≤zeroSpace A 8 := B.firstCover.carrier_pure ho (by decide)
  have cl : H.map C≤H := carrier_clock
  have cap : finrank K (zeroSpace A 9)≤11 := by
    have d := S.nextRoom
    change finrank K (zeroSpace A 9)+_≤11 at d
    omega
  obtain ⟨w,V⟩ := five_hidden_staircase ha (by decide) S.separated S.middleDefects cap dim h8 cl
  have h7 : zeroSpace A 7=chain C H w 3 := V.flags 7 (by decide) (by decide)
  have e : zeroSpace A 8=zeroSpace A 7⊔K∙(C^3) w := by
    rw [V.midpoint,h7]
    rfl
  have grow := zeroSpace_rank_interval_of_separation ha S.separated (j:=7) (d:=1)
    (by decide) (by decide)
  change finrank K (zeroSpace A 7)+1≤finrank K (zeroSpace A 8) at grow
  have mid : finrank K (zeroSpace A 8)=9 := S.middleDefects
  by_cases x : (C^3) w∈zeroSpace A 7
  · rw [sup_eq_left.mpr ((Submodule.span_singleton_le_iff_mem ..).mpr x)] at e
    rw [←e] at grow
    omega
  · rw [e,Submodule.finrank_sup_span_singleton x] at mid
    omega

theorem WideLinear.ann_seven_rank (B : WideLinear A b)
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 17 A b)
    (S : OddBalancedFrame A b 8 2) : finrank K (annih (treeSpace A 7))=10 := by
  have e := treeSpace_rank_eq_of_separation ho (q:=7) (by decide) (coeff_separated ho (by decide))
  rw [B.forward_seven ha ho S] at e
  have q := finrank_annih (treeSpace A 7)
  rw [Fintype.card_fin] at q
  omega

end
end RKResearch.Certified.ERK17
