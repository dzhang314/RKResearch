module

public import RKCert.CoreSupport
public import RKCert.OrderTwelveFeatureCount
public import RKCert.OrderTwelveMeshPolynomials

@[expose] public section
namespace RKCert.Paired.OrderTwelve
open RKCert.Paired RKCert.Paired.Clock RKCert.OneEscape Polynomial Module
variable {K:Type*} [Field K] {s:ℕ}

/-- A core key is the whole evaluation functional on the invariant algebra,
not merely the value of one chosen column at a row. -/
def coreKey (U:Submodule K (Vec K s)) (j:Fin s) (v:U) : K := v.val j
noncomputable def coreKeys (U:Submodule K (Vec K s)) : Finset (U→K) :=
  by classical exact (Finset.univ.filter (Live U)).image (coreKey U)

theorem coreKey_mem {U:Submodule K (Vec K s)} {i:Fin s} (hi:Live U i) :
    coreKey U i∈coreKeys U := by
  classical exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩)

theorem coreKey_node {U:Submodule K (Vec K s)} {c:Vec K s}
    (hC:U.map (diag c)≤U) {i j:Fin s}
    (hi:Live U i) (he:coreKey U i=coreKey U j) : c i=c j := by
  obtain ⟨v,hv,hvn⟩:=hi
  have e0 : v i=v j := congrFun he ⟨v,hv⟩
  have e1 : c i*v i=c j*v j :=
    congrFun he ⟨diag c v,hC (Submodule.mem_map_of_mem hv)⟩
  rw [←e0] at e1
  exact mul_right_cancel₀ hvn e1

private theorem coreKey_indicator {U:Submodule K (Vec K s)} (h:MulClosed U)
    {a:U→K} (ha:a∈coreKeys U) :
    ∃ v:U, ∀ j, v.val j=(by classical exact if coreKey U j=a then 1 else 0) := by
  classical
  obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp ha
  have hli:Live U i := (Finset.mem_filter.mp hi).2
  obtain ⟨e,he,eh⟩:=core_indicator h
  have e_i : e i=1 := by simp [eh,hli]
  have step (T:Finset (Fin s)) :
      ∃ v∈U, v i=1 ∧ ∀ j∈T, coreKey U j≠coreKey U i → v j=0 := by
    induction T using Finset.induction_on with
    | empty => exact ⟨e,he,e_i,by simp⟩
    | @insert k T _ ih =>
      obtain ⟨v,hv,hvi,hvT⟩:=ih
      by_cases hk:coreKey U k=coreKey U i
      · refine ⟨v,hv,hvi,?_⟩
        intro j hj nn
        rcases Finset.mem_insert.mp hj with rfl|hj
        · exact (nn hk).elim
        · exact hvT j hj nn
      · obtain ⟨u,hu⟩:∃ u:U,u.val k≠u.val i := Function.ne_iff.mp hk
        by_cases hl:Live U k
        · let d := (u.val i-u.val k)⁻¹ • (u.val-u.val k • e)
          have hd : d∈U := U.smul_mem _ (U.sub_mem u.property (U.smul_mem _ he))
          have d_i : d i=1 := by
            dsimp [d]
            simp only [e_i,mul_one]
            exact inv_mul_cancel₀ (sub_ne_zero.mpr hu.symm)
          have d_k : d k=0 := by simp [d,eh,hl]
          refine ⟨v*d,h _ hv _ hd,by simp [hvi,d_i],?_⟩
          intro j hj nn
          rcases Finset.mem_insert.mp hj with rfl|hj
          · simp [d_k]
          · simp [hvT j hj nn]
        · refine ⟨v,hv,hvi,?_⟩
          intro j hj nn
          rcases Finset.mem_insert.mp hj with rfl|hj
          · by_contra hz
            exact hl ⟨v,hv,hz⟩
          · exact hvT j hj nn
  obtain ⟨v,hv,hi,hz⟩:=step Finset.univ
  refine ⟨⟨v,hv⟩,fun j => ?_⟩
  by_cases hj:coreKey U j=coreKey U i
  · have ee: v j=v i := congrFun hj ⟨v,hv⟩
    simp [hj,ee,hi]
  · simp [hj,hz j (Finset.mem_univ _) hj]

theorem coreKeys_card_le {U:Submodule K (Vec K s)} (h:MulClosed U) :
    (coreKeys U).card≤finrank K U := by
  classical
  choose v hv using (fun a : coreKeys U => coreKey_indicator h a.property)
  let L : (coreKeys U→K)→ₗ[K] U := Fintype.linearCombination K v
  have hL : Function.Injective L := (injective_iff_map_eq_zero _).mpr (by
    intro c hc
    ext a
    obtain ⟨i,hi,ee⟩:=Finset.mem_image.mp a.property
    have ev := congrArg (fun u:U=>u.val i) hc
    have eq : (L c).val i=c a := by
      simp only [L,Fintype.linearCombination_apply,Submodule.coe_sum,Finset.sum_apply,
        Submodule.coe_smul,Pi.smul_apply,smul_eq_mul]
      rw [Finset.sum_eq_single a]
      · rw [hv a i,ee];simp
      · intro j _ hj
        have hne : (a:U→K)≠(j:U→K) := fun jh=>hj (Subtype.ext jh.symm)
        rw [hv j i,ee]
        simp [hne]
      · simp
    rw [eq] at ev
    exact ev)
  simpa only [Module.finrank_pi, Fintype.card_coe] using LinearMap.finrank_le_finrank_of_injective hL

noncomputable def headFeatures (c w:Vec K s) : Finset (K×K) :=
  by classical exact (Finset.univ.filter (fun j=>w j≠0)).image (fun j=>(c j,w j))
noncomputable def offFeatures (U:Submodule K (Vec K s)) (c w:Vec K s) : Finset K :=
  by classical exact (Finset.univ.filter (fun j=>¬Live U j ∧ w j=0)).image c

/-- All physical rows are distinguished by the three classes of features when
the band spans the full ambient space. This is a counting assertion about
physical stages, not an assertion that the numerical clock is distinct. -/
theorem count_by_features {A:Fin (s+1)→Fin (s+1)→K}
    (U : Submodule K (Vec K (s+1))) (w:Vec K (s+1)) (n:ℕ)
    (hinv:U.map (diag (nodes A))≤U) (hU:MulClosed U)
    (hdis:∀ i,Live U i→w i=0)
    (htop:pBand A ⊔ chain (diag (nodes A)) U w n=⊤) :
    s+1≤finrank K U+(headFeatures (nodes A) w).card+(offFeatures U (nodes A) w).card := by
  classical
  let c:=nodes A
  let S:=headFeatures c w
  let R:=offFeatures U c w
  let key : Fin (s+1)→coreKeys U ⊕ (S ⊕ R) := fun j =>
    if h : Live U j then .inl ⟨coreKey U j,coreKey_mem h⟩
    else if hw:w j≠0 then .inr (.inl ⟨(c j,w j),Finset.mem_image_of_mem _
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hw⟩)⟩)
    else .inr (.inr ⟨c j,Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h,not_ne_iff.mp hw⟩)⟩)
  have features (i j:Fin (s+1)) (e:key i=key j) :
      c i=c j ∧ w i=w j ∧ ∀ v∈U,v i=v j := by
    have iz (k:Fin (s+1)) (hk:¬Live U k) (v:Vec K (s+1)) (hv:v∈U) : v k=0 := by
      by_contra hn;exact hk ⟨v,hv,hn⟩
    unfold key at e
    split at e
    · rename_i hi
      split at e
      · rename_i hj
        have ee : coreKey U i=coreKey U j := congrArg Subtype.val (Sum.inl.inj e)
        exact ⟨coreKey_node hinv hi ee,(hdis i hi).trans (hdis j hj).symm,fun v hv=>congrFun ee ⟨v,hv⟩⟩
      · split at e <;> contradiction
    · rename_i hi
      split at e
      · rename_i hwi
        split at e
        · contradiction
        · rename_i hj
          split at e
          · rename_i hwj
            have ee : (c i,w i)=(c j,w j) := congrArg Subtype.val (Sum.inl.inj (Sum.inr.inj e))
            exact ⟨congrArg Prod.fst ee,congrArg Prod.snd ee,fun v hv=>(iz i hi v hv).trans (iz j hj v hv).symm⟩
          · cases Sum.inr.inj e
      · rename_i hwi
        split at e
        · contradiction
        · rename_i hj
          split at e
          · cases Sum.inr.inj e
          · rename_i hwj
            exact ⟨congrArg Subtype.val (Sum.inr.inj (Sum.inr.inj e)),
              (not_ne_iff.mp hwi).trans (not_ne_iff.mp hwj).symm,
              fun v hv=>(iz i hi v hv).trans (iz j hj v hv).symm⟩
  have kinj : Function.Injective key := by
    intro i j hs
    obtain ⟨hc,hw,hu⟩:=features i j hs
    have hc' : nodes A i=nodes A j := hc
    have heq (v:Vec K (s+1)) : v i=v j := by
      have h : v∈pBand A ⊔ chain (diag c) U w n := by rw [htop];trivial
      obtain ⟨_,⟨a,rfl⟩,z,hz,rfl⟩:=Submodule.mem_sup.mp h
      obtain ⟨u,hu',Q,_,eq⟩:=exists_head_poly hz
      rw [Pi.add_apply,Pi.add_apply,polyEval_at,polyEval_at,eq i,eq j,hc',hc,hw,hu u hu']
    by_contra hne
    have hh := heq (Pi.single i 1)
    simp [Ne.symm hne] at hh
  have hc := Fintype.card_le_of_injective key kinj
  simp only [Fintype.card_fin,Fintype.card_sum,Fintype.card_coe] at hc
  have hu := coreKeys_card_le hU
  change s+1≤(coreKeys U).card+((headFeatures (nodes A) w).card+(offFeatures U (nodes A) w).card) at hc
  omega

end RKCert.Paired.OrderTwelve

