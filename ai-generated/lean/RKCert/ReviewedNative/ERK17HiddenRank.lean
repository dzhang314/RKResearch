module

public import RKCert.ReviewedNative.ERK17HiddenFrame
public import RKCert.ReviewedNative.HiddenFourDispatch

@[expose] public section

/-! # The actual order-17 zero-seed hidden carrier has rank exactly five -/
namespace RKResearch.Certified.ERK17
open RKResearch Polynomial Module RKCert.Endpoint RKCert.Endpoint.WeightedClock
open RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse
open RKResearch.Certified.Graded.Reverse.Thin
open RKCert.OneEscape
open scoped Classical

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A : Matrix (Fin 26) (Fin 26) K} {b : Fin 26→K}

set_option maxRecDepth 3500
set_option maxHeartbeats 850000

theorem width26_no_four_hidden (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 17 A b)
    (S : OddBalancedFrame A b 8 2) (Z : Width26QuadraticCover A b)
    (F : HiddenFrame A b) (dimH : finrank K (hiddenCarrier A b)=4) : False := by
  classical
  let : DecidableEq K:=Classical.decEq K
  let t:=Fin.last 25
  let c:=nodes A
  let d:=quadraticSeed A b
  let y:=reflectedClock A
  let H := hiddenCarrier A b
  let V := visible A b
  have cap : finrank K (zeroSpace A 9)≤11 := by
    have h := S.nextRoom
    change finrank K (zeroSpace A 9)+_≤11 at h
    omega
  have y0 : y t=0 := by change 1-nodes A t=0; rw [Z.lastClock,sub_self]
  have col (k : Fin 26) : A k t=0 := ha k t (Fin.le_last k)
  have big : 7<(weightedSites y d).card := Z.sites
  have cov := Z.pointwise
  have off : SupportsComplement A b 8 t := supportsComplement_of_cover cov
  have hb := F.invisible
  have detect := F.detected
  refine four_hidden_rank_dispatch ha (by decide) S.separated S.middleDefects cap
    H F.toEight dimH F.stable V hb detect ?_ ?_
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
    refine detect v (zeroSpace_mono A (by decide:6≤8) hv) (fun i vi=>?_ )
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
    have wq:w∈zeroSpace A 8:=by
      have z:=powers 0 (by omega)
      rw [pow_zero,one_apply_eq_self] at z
      exact sup_le (zeroSpace_mono A (by omega:j≤8)) F.toEight z
    have reps (a:ℕ)(al:a≤j-4):∃f:(Fin 26→K),f∈zeroSpace A j ∧
        ∀i,V i→f i=c i^a*w i:=by
      obtain ⟨f,hf,u,hu,eq⟩:=Submodule.mem_sup.mp (powers a (by omega))
      refine ⟨f,hf,?_⟩
      intro i vi
      have e:=congrFun eq i
      rw [Pi.add_apply,hb _ hu _ vi,add_zero,HeadFiber.clock_power_value] at e
      exact e
    let fam(a:ℕ):(Fin 26→K):=if h:a≤j-4 then Classical.choose (reps a h) else 0
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
theorem width26_hidden_rank_lower (ha : ∀ i j,i≤j → A i j=0)
    (S : OddBalancedFrame A b 8 2) (H : HiddenFrame A b) :
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
  have sep := (PolySeparated.of_coeff S.separated).mono (by decide : 4≤8)
  have g := clock_invariant_incoming ha (j:=3) sep inv
  change finrank K (zeroSpace A 3)+2≤finrank K (zeroSpace A 4) at g
  omega

theorem width26_hidden_rank_five (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 17 A b)
    (S : OddBalancedFrame A b 8 2) (Z : Width26QuadraticCover A b)
    (H : HiddenFrame A b) : finrank K (hiddenCarrier A b)=5 := by
  have lo := width26_hidden_rank_lower ha S H
  have hi := H.rankCap
  by_contra! bad
  exact width26_no_four_hidden ha ho S Z H (by omega)

theorem ordered_width26_hidden_rank_five (ha : ∀ i j,i≤j → A i j=0)
    (ho : HasOrder 17 A b) (z : firstSeed A b=0) : finrank K (hiddenCarrier A b)=5 := by
  let S := (ordered_width26_full_frame ha ho).1
  let Z := ordered_width26_quadratic_cover ha ho z
  exact width26_hidden_rank_five ha ho S Z (width26_hidden_frame ha ho S Z)

end RKResearch.Certified.ERK17
