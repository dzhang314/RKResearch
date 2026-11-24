module

public import RKCert.ReviewedNative.ERK19ReverseCover
public import RKCert.ReviewedNative.NativeHiddenCarrier
public import RKCert.ReviewedNative.ReversePhysicalPorts
public import RKCert.ReviewedNative.HiddenFourDispatch
public import RKCert.ReviewedNative.FiveHiddenHead

public section

/-! # Native order-nineteen zero-seed carrier at width twenty-nine

The paid degree-seven reverse cover uses the original rows. The same
four-grade visibility proof and four-carrier dispatch force five
compensated blind coordinates and the true forward single head.
-/
namespace RKResearch.Certified.ERK19

open RKResearch Polynomial Module RKCert.Endpoint RKCert.Endpoint.WeightedClock
open RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse
open RKResearch.Certified.Graded.Reverse.Thin RKCert.OneEscape
open scoped Classical

noncomputable section
variable {K : Type*} [Field K]
variable {A : Matrix (Fin 29) (Fin 29) K} {b : Fin 29 → K}

abbrev hiddenCarrier (A : Matrix (Fin 29) (Fin 29) K) (b : Fin 29 → K) :=
  Hidden.carrier (nodes A) b (quadraticSeed A b) 0 (Fin.last 28)

def visible (A : Matrix (Fin 29) (Fin 29) K) (b : Fin 29 → K) (i : Fin 29) : Prop :=
  quadraticSeed A b i≠0 ∨ reflectedClock A i*b i≠0

structure Width29ZeroCover (A : Matrix (Fin 29) (Fin 29) K) (b : Fin 29 → K) : Prop where
  lastLive : b (Fin.last 28)≠0
  lastClock : nodes A (Fin.last 28)=1
  lastSeed : quadraticSeed A b (Fin.last 28)=0
  sites : 8<(weightedSites (reflectedClock A) (quadraticSeed A b)).card
  pointwise : ∀ v∈zeroAt (annih (treeSpace A 9)) (Fin.last 28), ∃ P : K[X],
    P.natDegree≤7 ∧ weightedEval (reflectedClock A) (quadraticSeed A b) P=v

structure Width29HiddenFrame (A : Matrix (Fin 29) (Fin 29) K) (b : Fin 29 → K) : Prop where
  fromFour : zeroSpace A 4≤hiddenCarrier A b
  toNine : hiddenCarrier A b≤zeroSpace A 9
  stable : (hiddenCarrier A b).map (diag (nodes A))≤hiddenCarrier A b
  rankCap : finrank K (hiddenCarrier A b)≤5
  invisible : ∀ v∈hiddenCarrier A b, ∀ i, visible A b i → v i=0
  detected : ∀ v∈zeroSpace A 9, (∀i,visible A b i→v i=0) → v∈hiddenCarrier A b

variable [LinearOrder K] [IsStrictOrderedRing K]

/-- Polynomial representatives of the already verified true cover.
This does not redo the quadratic support stand-alone argument. -/
theorem width29_zero_cover_data (ha : ∀ i k, i≤k → A i k=0) (ho : HasOrder 19 A b)
    (zero : firstSeed A b=0) : Width29ZeroCover A b := by
  obtain ⟨live,clock,seed,_,_⟩ := width29_zero_terminal ha ho zero
  obtain ⟨sites,cov⟩ := width29_zero_quadratic_cover ha ho zero
  refine ⟨live,clock,seed,sites,fun v hv => ?_⟩
  rw [cov] at hv
  obtain ⟨P,d,rfl⟩ := mem_weightedBand.mp hv
  refine ⟨P,?_,rfl⟩
  by_cases z : P=0
  · simp [z]
  · have g := (natDegree_lt_iff_degree_lt z).mpr d
    omega

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem width29_F10_cap (S : OddBalancedFrame A b 9 2) :
    finrank K (zeroSpace A 10)≤12 := by
  have e := S.nextRoom
  change finrank K (zeroSpace A 10)+_≤12 at e
  omega

set_option maxHeartbeats 650000 in
theorem width29_hidden_frame_from_cover (ha : ∀ i k, i≤k → A i k=0)
    (ho : HasOrder 19 A b) (S : OddBalancedFrame A b 9 2) (Z : Width29ZeroCover A b) :
    Width29HiddenFrame A b := by
  let t := Fin.last 28
  have zt : reflectedClock A t=0 := by change 1-nodes A t=0; rw [Z.lastClock,sub_self]
  have col (k : Fin 29) : A k t=0 := ha k t (Fin.le_last k)
  have off : SupportsComplement A b 9 t := supportsComplement_of_cover Z.pointwise
  have ins : hiddenCarrier A b≤zeroSpace A 9 :=
    Hidden.carrier_le_defects ha ho (by decide) Z.lastClock Z.lastLive Z.lastSeed off
  have inv : (hiddenCarrier A b).map (diag (nodes A))≤hiddenCarrier A b :=
    Hidden.carrier_invariant Z.lastClock
  have blind (v : Fin 29 → K) (hv : v∈hiddenCarrier A b) (i : Fin 29) (vi : visible A b i) :
      v i=0 := by
    rcases vi with d|y
    · exact Hidden.carrier_zero_on_active Z.lastSeed hv d
    · exact (mul_eq_zero.mp (Hidden.carrier_mirror_weight_zero Z.lastClock hv i)).resolve_left y
  have det (v : Fin 29 → K) (hv : v∈zeroSpace A 9) (h : ∀ i, visible A b i→v i=0) :
      v∈hiddenCarrier A b := by
    apply Hidden.actual_defect_hidden ha ho (by decide) hv
    · intro i
      by_cases d : quadraticSeed A b i=0
      · rw [d,zero_mul]
      · rw [h i (Or.inl d),mul_zero]
    · intro i
      change (reflectedClock A i*b i)*v i=0
      by_cases d : reflectedClock A i*b i=0
      · rw [d,zero_mul]
      · rw [h i (Or.inr d),mul_zero]
  refine ⟨?_,ins,inv,invariant_core_cap_of_rank ha (by decide) S.separated S.middleDefects
    (width29_F10_cap S) _ ins inv,blind,det⟩
  intro v hv
  obtain ⟨Q,P,qd,pd,qfit,pfit⟩ := thin_reverse_two_traces ho hv
    (by decide) (by decide) (by decide) t zt Z.lastSeed Z.sites Z.pointwise
  have van := ordered_thin_invisible_given_reps ha ho zt col off Q P qd
    (by omega) (by omega) (by omega) (by omega) qfit pfit
  exact Hidden.actual_defect_hidden ha ho (by decide) hv (fun i => (van i).1) (fun i => (van i).2)

theorem width29_hidden_frame (ha : ∀ i k, i≤k → A i k=0) (ho : HasOrder 19 A b)
    (zero : firstSeed A b=0) : Width29HiddenFrame A b :=
  width29_hidden_frame_from_cover ha ho (ordered_width29_frame ha ho).1 (width29_zero_cover_data ha ho zero)

set_option maxRecDepth 3500
set_option maxHeartbeats 850000

theorem width29_no_four_hidden (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 19 A b)
    (S : OddBalancedFrame A b 9 2) (Z : Width29ZeroCover A b)
    (F : Width29HiddenFrame A b) (dimH : finrank K (hiddenCarrier A b)=4) : False := by
  classical
  let : DecidableEq K:=Classical.decEq K
  let t:=Fin.last 28
  let c:=nodes A
  let d:=quadraticSeed A b
  let y:=reflectedClock A
  let H := hiddenCarrier A b
  let V := visible A b
  have cap : finrank K (zeroSpace A 10)≤12 := width29_F10_cap S
  have y0 : y t=0 := by change 1-nodes A t=0; rw [Z.lastClock,sub_self]
  have col (k : Fin 29) : A k t=0 := ha k t (Fin.le_last k)
  have big : 8<(weightedSites y d).card := Z.sites
  have cov := Z.pointwise
  have off : SupportsComplement A b 9 t := supportsComplement_of_cover cov
  have hb := F.invisible
  have detect := F.detected
  refine four_hidden_rank_dispatch ha (by decide) S.separated S.middleDefects cap
    H F.toNine dimH F.stable V hb detect ?_ ?_
  · rintro v hv ⟨a,sy⟩
    obtain ⟨Q,P,dQ,_,fitQ,fitP⟩:=thin_reverse_two_traces ho hv
      (by decide) (by decide) (by decide) t y0 Z.lastSeed big cov
    let T:=(weightedSites y d).erase (1-a)
    have dc:7≤T.card:=by
      have cc:=Finset.pred_card_le_card_erase (s:=weightedSites y d) (a:=1-a)
      change (weightedSites y d).card-1≤T.card at cc
      omega
    have qz:Q=0:=by
      apply eq_of_degrees_lt_of_eval_finset_eq T
      · exact degree_le_natDegree.trans_lt (by exact_mod_cast (show Q.natDegree<T.card by omega))
      · exact degree_le_natDegree.trans_lt (by rw [natDegree_zero];exact_mod_cast (show 0<T.card by omega))
      intro x hx
      obtain ⟨nx,z⟩:=Finset.mem_erase.mp hx
      obtain ⟨i,dz,rfl⟩:=mem_weightedSites.mp z
      have loc:c i≠a:=fun e=>nx (by change 1-c i=1-a;rw [e])
      have ne:Q.eval (y i)*d i=0:=by
        rw [←fitQ i,sy i (Or.inl dz) loc,mul_zero]
      rw [eval_zero]
      exact (mul_eq_zero.mp ne).resolve_right dz
    refine detect v (zeroSpace_mono A (by decide:6≤9) hv) (fun i vi=>?_ )
    have q:=fitQ i
    rw [qz,eval_zero,zero_mul] at q
    by_cases dz:d i=0
    · have bf:=fitP i
      rw [show quadraticSeed A b i=0 from dz,mul_zero] at bf
      rcases vi with e|e
      · exact False.elim (e dz)
      · exact (mul_eq_zero.mp bf).resolve_left e
    · exact (mul_eq_zero.mp q).resolve_left dz
  · intro j small w powers
    have j5:5≤j:=by rcases small with e|e <;> omega
    have j6:j≤6:=by rcases small with e|e <;> omega
    have wq:w∈zeroSpace A 9:=by
      have z:=powers 0 (by omega)
      rw [pow_zero,one_apply_eq_self] at z
      exact sup_le (zeroSpace_mono A (by omega:j≤9)) F.toNine z
    have reps (a:ℕ)(al:a≤j-4):∃f:(Fin 29→K),f∈zeroSpace A j ∧
        ∀i,V i→f i=c i^a*w i:=by
      obtain ⟨f,hf,u,hu,eq⟩:=Submodule.mem_sup.mp (powers a (by omega))
      refine ⟨f,hf,?_⟩
      intro i vi
      have e:=congrFun eq i
      rw [Pi.add_apply,hb _ hu _ vi,add_zero,HeadFiber.clock_power_value] at e
      exact e
    let fam(a:ℕ):(Fin 29→K):=if h:a≤j-4 then Classical.choose (reps a h) else 0
    have E(a:ℕ)(h:a≤j-4):fam a∈zeroSpace A j ∧ ∀i,V i→fam a i=c i^a*w i:=by
      rw [show fam a=Classical.choose (reps a h) from dite_eq_left h]
      exact Classical.choose_spec (reps a h)
    obtain ⟨Q,P,dQ,dP,fitQ,fitP⟩:=thin_reverse_traces_same_grade_drop ho
      (j:=j) (by omega) (by omega) (by decide) t y0 Z.lastSeed big cov fam
      (fun a h=>(E a h).1) (fun a h i vi=>(E a h).2 i vi)
    have van:=ordered_thin_invisible_given_reps ha ho y0 col off Q P (by omega)
      (by omega) (by omega) (by omega) (by omega) fitQ fitP
    refine detect w wq (fun i hi=>?_ )
    rcases hi with e|e
    · exact (mul_eq_zero.mp (van i).1).resolve_left e
    · exact (mul_eq_zero.mp (van i).2).resolve_left e

/-- Rank three would make the already paid F4 invariant. Its incoming
Hermite gain of two itself supplies the lower bound of four. -/
theorem width29_hidden_rank_lower (ha : ∀ i j,i≤j → A i j=0)
    (S : OddBalancedFrame A b 9 2) (H : Width29HiddenFrame A b) :
    4≤finrank K (hiddenCarrier A b) := by
  have d3 := zeroSpace_rank_interval_of_separation ha S.separated (j:=1) (d:=2)
    (by decide) (by decide)
  have d4 := zeroSpace_rank_interval_of_separation ha S.separated (j:=1) (d:=3)
    (by decide) (by decide)
  have inc := Submodule.finrank_mono H.fromFour
  change _+2≤finrank K (zeroSpace A 3) at d3
  change _+3≤finrank K (zeroSpace A 4) at d4
  by_contra! small
  have e : zeroSpace A 4=hiddenCarrier A b :=
    Submodule.eq_of_le_of_finrank_le H.fromFour (by omega)
  have inv : (zeroSpace A 4).map (diag (nodes A))≤zeroSpace A 4 := by rw [e]; exact H.stable
  have sep := (PolySeparated.of_coeff S.separated).mono (by decide : 4≤9)
  have g := clock_invariant_incoming ha (j:=3) sep inv
  change finrank K (zeroSpace A 3)+2≤finrank K (zeroSpace A 4) at g
  omega

theorem width29_hidden_rank_five (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 19 A b)
    (S : OddBalancedFrame A b 9 2) (Z : Width29ZeroCover A b)
    (H : Width29HiddenFrame A b) : finrank K (hiddenCarrier A b)=5 := by
  have lo := width29_hidden_rank_lower ha S H
  have hi := H.rankCap
  by_contra! bad
  exact width29_no_four_hidden ha ho S Z H (by omega)

theorem ordered_width29_hidden_rank_five (ha : ∀ i j,i≤j → A i j=0)
    (ho : HasOrder 19 A b) (z : firstSeed A b=0) : finrank K (hiddenCarrier A b)=5 := by
  let S := (ordered_width29_frame ha ho).1
  let Z := width29_zero_cover_data ha ho z
  exact width29_hidden_rank_five ha ho S Z (width29_hidden_frame_from_cover ha ho S Z)



/-- At the physical cap the five-dimensional hidden carrier is the
same true rank-five core used in the full native F6–F9 staircase. -/
theorem width29_zero_hidden_staircase (ha : ∀ i k, i≤k → A i k=0) (ho : HasOrder 19 A b)
    (zero : firstSeed A b=0) :
    ∃ w, FiveHiddenStaircase A 9 (hiddenCarrier A b) w := by
  have S := (ordered_width29_frame ha ho).1
  have Z := width29_zero_cover_data ha ho zero
  have H := width29_hidden_frame_from_cover ha ho S Z
  exact five_hidden_staircase ha (by decide) S.separated S.middleDefects
    (width29_F10_cap S) (width29_hidden_rank_five ha ho S Z H) H.toNine H.stable

end
end RKResearch.Certified.ERK19

