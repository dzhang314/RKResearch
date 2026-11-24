module
public import RKCert.ERKOddVisibleFeeders

@[expose] public section
/-! # Genuine four-hidden exclusion at the zero-seed order-17 boundary -/
namespace RKCert.Paired.ERKOddHidden
open RKCert.Paired.FiniteMidpoint RKCert.Paired.ReverseHull RKCert.Paired.ERKEvenHidden
open RKCert.Paired.Clock RKCert.Endpoint Polynomial Module
variable {K:Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A:Fin 26→Fin 26→K} {b:Vec K 26}

set_option maxHeartbeats 2600000 in
theorem odd17_no_four_hidden (ha:StrictLower A)(ho:HasTreeOrderAtLeast A b 17)
    (S:OddBalanced (s:=25) A b 8)(Z:OddZeroReverse (s:=25) A b 8)
    (dimH:finrank K (carrier (nodes A) b (backSeed2 A b) 0 (Fin.last 25))=4) : False :=by
  classical
  let : DecidableEq K:=Classical.decEq K
  let t:=Fin.last 25
  let c:=nodes A
  let d:=backSeed2 A b
  let y:=mirror A
  let H:=carrier c b d 0 t
  let V:=oddVisible A b
  obtain ⟨_,HF,HI⟩:=balanced_odd_hidden_zero ha ho (by decide) S Z
  have cap:finrank K (zeroSpace A 9)≤11:=by have e:=S.nextCap;change finrank K (zeroSpace A 9)+_≤11 at e;omega
  have y0:y t=0:=S.lastReflect Z.firstZero
  have col:∀ k,A k t=0:=fun k=>ha k _ (Fin.le_last k)
  have big:7<(headSites y d).card:=Z.sites
  have cov:∀v∈annih (treeSpace A 8)⊓LinearMap.ker (LinearMap.proj t),
      ∃P:K[X],P.natDegree≤6 ∧ weightedEval y d P=v:=
    fun _ hv=>Z.poly_cover (by decide) hv
  have off:SupportsComplement A b 8 t:=by
    intro v hv i hi
    obtain ⟨T,_,e⟩:=cov v hv
    change d i=0 at hi
    rw [←e,weightedEval_apply,hi,mul_zero]
  have hb(v:Vec K 26)(hv:v∈H)(i:Fin 26)(hi:V i):v i=0:=by
    rcases hi with h|h
    · exact carrier_zero_on_active Z.lastSeed hv h
    · exact (mul_eq_zero.mp (carrier_mirror_weight_zero Z.lastNode hv i)).resolve_left h
  have detect(v:Vec K 26)(hv:v∈zeroSpace A 8)(h:∀i,V i→v i=0):v∈H:=by
    apply actual_defect_hidden ha ho (by decide) hv
    · intro i
      by_cases e:d i=0
      · exact congrArg (fun a:K=>a*v i) e |>.trans (zero_mul _)
      · rw [h i (Or.inl e),mul_zero]
    · intro i
      change y i*b i*v i=0
      by_cases e:y i*b i=0
      · rw [e,zero_mul]
      · rw [h i (Or.inr e),mul_zero]
  refine four_hidden_rank_dispatch ha ho (by decide) (by decide) S.separated S.forwardMid cap H HF dimH HI V hb detect ?_ ?_
  · rintro v hv ⟨a,sy⟩
    obtain ⟨Q,P,dQ,_,fitQ,fitP⟩:=thin_reverse_two_traces ho hv
      (by decide) (by decide) (by decide) t y0 Z.lastSeed big cov
    let T:=(headSites y d).erase (1-a)
    have dc:7≤T.card:=by
      have cc:=Finset.pred_card_le_card_erase (s:=headSites y d) (a:=1-a)
      change (headSites y d).card-1≤T.card at cc
      omega
    have qz:Q=0:=by
      apply eq_of_degrees_lt_of_eval_finset_eq T
      · exact degree_le_natDegree.trans_lt (by exact_mod_cast (show Q.natDegree<T.card by omega))
      · exact degree_le_natDegree.trans_lt (by rw [natDegree_zero];exact_mod_cast (show 0<T.card by omega))
      intro x hx
      obtain ⟨nx,z⟩:=Finset.mem_erase.mp hx
      obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp z
      have dz:d i≠0:=(Finset.mem_filter.mp hi).2
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
      rw [show backSeed2 A b i=0 from dz,mul_zero] at bf
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
      exact sup_le (zeroSpace_mono A (by omega:j≤8)) HF z
    have reps (a:ℕ)(al:a≤j-4):∃f:Vec K 26,f∈zeroSpace A j ∧
        ∀i,V i→f i=c i^a*w i:=by
      obtain ⟨f,hf,u,hu,eq⟩:=Submodule.mem_sup.mp (powers a (by omega))
      refine ⟨f,hf,?_⟩
      intro i vi
      have e:=congrFun eq i
      rw [Pi.add_apply,hb _ hu _ vi,add_zero,pow_diag_apply] at e
      exact e
    let fam(a:ℕ):Vec K 26:=if h:a≤j-4 then Classical.choose (reps a h) else 0
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

/-- The true stage-compensated kernel must reach the last remaining
five-hidden case; these are dimensions, not untrimmed stage counts. -/
theorem odd17_hidden_rank_five (ha:StrictLower A)(ho:HasTreeOrderAtLeast A b 17)
    (S:OddBalanced (s:=25) A b 8)(Z:OddZeroReverse (s:=25) A b 8) :
    finrank K (carrier (nodes A) b (backSeed2 A b) 0 (Fin.last 25))=5:=by
  obtain ⟨F4,H8,inv⟩:=balanced_odd_hidden_zero ha ho (by decide) S Z
  have cap:finrank K (zeroSpace A 9)≤11:=by have e:=S.nextCap;change finrank K (zeroSpace A 9)+_≤11 at e;omega
  have up:=invariant_core_cap_of_rank ha ho (by decide) (by decide) S.separated S.forwardMid cap _ H8 inv
  have fd:=odd17_two_visible_feeders ha ho S Z F4
  have g:=strict_rank_interval ha S.separated 1 2 (by decide) (by decide)
  let H:=carrier (nodes A) b (backSeed2 A b) 0 (Fin.last 25)
  change finrank K H=5
  change finrank K H≤5 at up
  change finrank K (zeroSpace A 3)+2≤finrank K H at fd
  change finrank K (zeroSpace A 1)+2≤finrank K (zeroSpace A 3) at g
  by_contra h
  apply odd17_no_four_hidden ha ho S Z
  change finrank K H=4
  omega

end RKCert.Paired.ERKOddHidden

