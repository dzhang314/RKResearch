module
public import RKCert.OrderTwelveCoreRows
public import RKCert.ERKOwnerCompression

@[expose] public section
/-! # Earliest literal stage classes at a sharp feature cardinality
Unlike general coordinate elimination, this uses exactly one retained row
per physical feature. It consequently preserves actual products and all
moments on coordinatewise expressions in the retained class algebra.
-/
namespace RKCert.Paired.OwnerCompression
open RKCert.Paired.OrderTwelve RKCert.Paired.Clock RKCert.OneEscape Module
variable {K:Type*} [Field K] {s r:ℕ}
set_option maxHeartbeats 2000000

theorem earliest_representatives {ι:Type*} [Fintype ι] (key:Fin s→ι)
    (H:Submodule K (Vec K s)) (rank:finrank K H=r) (cap:Fintype.card ι≤r)
    (matched:∀ i j,key i=key j→∀ v∈H,v i=v j) :
    ∃ (e:Fin r ↪o Fin s) (owner:Fin s→Fin r),
      (∀ i, e (owner i) ≤ i) ∧ (∀ v∈H,∀i,v (e (owner i))=v i) ∧ ∀ j,owner (e j)=j := by
  classical
  let X (i:Fin s) := Finset.univ.filter (fun j=>key j=key i)
  have ex (i:Fin s) : (X i).Nonempty := ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩⟩
  let rep (i:Fin s) := (X i).min' (ex i)
  have keyrep (i:Fin s) : key (rep i)=key i := (Finset.mem_filter.mp ((X i).min'_mem (ex i))).2
  have early (i:Fin s) : rep i ≤ i := (X i).min'_le _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩)
  have same {i j:Fin s} (h:key i=key j) : rep i=rep j := by
    apply le_antisymm
    · exact (X i).min'_le _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,(keyrep j).trans h.symm⟩)
    · exact (X j).min'_le _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,(keyrep i).trans h⟩)
  let S := Finset.univ.image rep
  have occurs (i:Fin s) : rep i∈S := Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have upper : S.card≤r := by
    have hinj : Function.Injective (fun i:S=>key i.val) := by
      intro i j he
      rcases Finset.mem_image.mp i.property with ⟨k,_,hk⟩
      rcases Finset.mem_image.mp j.property with ⟨l,_,hl⟩
      apply Subtype.ext
      rw [←hk,←hl]
      change key i.val=key j.val at he
      rw [←hk,←hl,keyrep,keyrep] at he
      exact same he
    exact ((by simpa only [Fintype.card_coe] using Fintype.card_le_of_injective _ hinj) : S.card≤Fintype.card ι).trans cap
  let T : H→ₗ[K] (S→K) :=
    {toFun:=fun v i=>v.val i.val
     map_add':=by intro x y;rfl
     map_smul':=by intro a x;rfl}
  have Ti : Function.Injective T := by
    intro v w he
    apply Subtype.ext
    ext i
    have zz := congrFun he ⟨rep i,occurs i⟩
    change v.val (rep i)=w.val (rep i) at zz
    rwa [matched _ _ (keyrep i) v.val v.property,matched _ _ (keyrep i) w.val w.property] at zz
  have lower : r≤S.card := by
    have hd:=T.finrank_le_finrank_of_injective Ti
    rwa [rank,Module.finrank_fintype_fun_eq_card,Fintype.card_coe] at hd
  let iso := S.orderIsoOfFin (le_antisymm upper lower)
  let e := S.orderEmbOfFin (le_antisymm upper lower)
  let own (i:Fin s) := iso.symm ⟨rep i,occurs i⟩
  have val (i:Fin s) : e (own i)=rep i := congrArg Subtype.val (iso.apply_symm_apply _)
  refine ⟨e,own,?_,?_,?_⟩
  · intro i
    rw [val]
    exact early i
  · intro v hv i
    rw [val]
    exact matched _ _ (keyrep i) v hv
  · intro j
    apply e.injective
    rw [val]
    have p:S.orderEmbOfFin (le_antisymm upper lower) j∈S := S.orderEmbOfFin_mem _ _
    obtain ⟨i,_,eq⟩:=Finset.mem_image.mp p
    change rep i=e j at eq
    rw [←eq]
    exact same (keyrep i)

variable {A:Fin s→Fin s→K}

/-- Sharp rank in any polynomial/head/core band gives a causal literal owner
family, even if neither numerical abscissae nor output weights distinguish
the stages. -/
theorem representatives_of_band (q m:ℕ) (U:Submodule K (Vec K s)) (w:Vec K s)
    (H:Submodule K (Vec K s)) (rank:finrank K H=r)
    (hi:U.map (diag (nodes A))≤U) (hU:MulClosed U) (dis:∀i,Live U i→w i=0)
    (band:H≤LinearMap.range (polyEval A q)⊔chain (diag (nodes A)) U w m)
    (cap:finrank K U+(headFeatures (nodes A) w).card+(offFeatures U (nodes A) w).card≤r) :
    ∃ (e:Fin r ↪o Fin s) (owner:Fin s→Fin r),
      (∀ i, e (owner i) ≤ i) ∧ (∀ v∈H,∀i,v (e (owner i))=v i) ∧ ∀ j,owner (e j)=j := by
  classical
  let c:=nodes A
  let S:=headFeatures c w
  let R:=offFeatures U c w
  let key : Fin s→coreKeys U ⊕ (S ⊕ R) := fun j =>
    if h : Live U j then .inl ⟨coreKey U j,coreKey_mem h⟩
    else if hw:w j≠0 then .inr (.inl ⟨(c j,w j),Finset.mem_image_of_mem _
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hw⟩)⟩)
    else .inr (.inr ⟨c j,Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h,not_ne_iff.mp hw⟩)⟩)
  have features (i j:Fin s) (e:key i=key j) :
      c i=c j ∧ w i=w j ∧ ∀ v∈U,v i=v j := by
    have iz (k:Fin s) (hk:¬Live U k) (v:Vec K s) (hv:v∈U) : v k=0 := by
      by_contra hn;exact hk ⟨v,hv,hn⟩
    unfold key at e
    split at e
    · rename_i bi
      split at e
      · rename_i bj
        have ee : coreKey U i=coreKey U j := congrArg Subtype.val (Sum.inl.inj e)
        exact ⟨coreKey_node hi bi ee,(dis i bi).trans (dis j bj).symm,fun v hv=>congrFun ee ⟨v,hv⟩⟩
      · split at e <;> contradiction
    · rename_i bi
      split at e
      · rename_i bwi
        split at e
        · contradiction
        · rename_i bj
          split at e
          · rename_i bwj
            have ee : (c i,w i)=(c j,w j) := congrArg Subtype.val (Sum.inl.inj (Sum.inr.inj e))
            exact ⟨congrArg Prod.fst ee,congrArg Prod.snd ee,fun v hv=>(iz i bi v hv).trans (iz j bj v hv).symm⟩
          · cases Sum.inr.inj e
      · rename_i bwi
        split at e
        · contradiction
        · rename_i bj
          split at e
          · cases Sum.inr.inj e
          · rename_i bwj
            exact ⟨congrArg Subtype.val (Sum.inr.inj (Sum.inr.inj e)),
              (not_ne_iff.mp bwi).trans (not_ne_iff.mp bwj).symm,
              fun v hv=>(iz i bi v hv).trans (iz j bj v hv).symm⟩
  apply earliest_representatives key H rank
  · have hu := coreKeys_card_le hU
    simp only [Fintype.card_sum,Fintype.card_coe]
    change (coreKeys U).card+(S.card+R.card)≤r
    change finrank K U+S.card+R.card≤r at cap
    omega
  · intro i j eq v hv
    obtain ⟨hc,hw,hu⟩:=features i j eq
    obtain ⟨_,⟨a,rfl⟩,z,hz,rfl⟩:=Submodule.mem_sup.mp (band hv)
    obtain ⟨u,hu',Q,_,he⟩:=exists_head_poly hz
    have hc' : nodes A i=nodes A j := hc
    simp only [Pi.add_apply,polyEval_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,normTree_bush]
    rw [he i,he j,hc',hw,hu u hu']

end RKCert.Paired.OwnerCompression
