module

public import RKCert.DirkDirtyPivot

@[expose] public section

/-! # Five genuine dirty rows forced onto the same three predecessors -/

namespace RKCert.Paired.Reduce
open RKCert.Paired.Clock RKCert.OneEscape RKCert.Endpoint Polynomial
open scoped Classical
noncomputable section

variable {K : Type*} [Field K] [CharZero K] {s p : ℕ}
variable {A : Fin s → Fin s → K} {b : Vec K s}
variable {U : Submodule K (Vec K s)} {w : Vec K s} {P : K[X]}

local notation "B" => foldMatrix A w U
local notation "c" => nodes A
local notation "D" => restrict c w U
local notation "R" => commutatorMatrix B c

set_option maxHeartbeats 1800000 in
theorem common_first_three (h : Grade3Head A U w P) (ha : LowerArray A)
    (ho : HasTreeOrderAtLeast A b p) (hp : 8 ≤ p) :
    ∃ d : Fin 5 → Fin s, StrictMono d ∧ (∀ i, Dirty c w U (d i)) ∧
      ∀ i : Fin 5, ∀ j : Fin s,
        (∀ k : Fin 3, j≠d (Fin.castLE (by decide) k)) → B (d i) j=0 := by
  obtain ⟨d,mono,dirty,exhaust⟩ := first_dirty_rows h (n:=5) (by decide)
  obtain ⟨u,hu,ufirst⟩ := exists_first_of (show ∃ i, Clean c w U i from
    (exists_clean_nonroot h ho hp).imp (fun _ hi => hi.1))
  let old₃ : Fin 3 → Fin s := fun k => d (Fin.castLE (by decide) k)
  let old₄ : Fin 4 → Fin s := fun k => d (Fin.castLE (by decide) k)
  let a := d 3
  let e := d 4
  have ha' : LowerArray B := foldMatrix_lower ha
  have hr' : LowerArray R := commutatorMatrix_lower ha'
  have mulR (v) (hv : mat R v=0) (i : Fin s) : mat R v i=0 := congrFun hv i
  have ea : a < e := mono (by decide : (3:Fin 5)<4)
  have strictOld (j : Fin s) (k : Fin 5) (hij : j < d k)
      (hj : Dirty c w U j) : ∃ l : Fin 5, d l=j ∧ l < k := by
    obtain ⟨l,hl,_⟩ := exhaust j hj k hij.le
    exact ⟨l,hl,mono.lt_iff_lt.mp (hl.symm ▸ hij)⟩
  have locate3 (j : Fin s) (hj : Dirty c w U j) (hlt : j < a) : j∈Set.range old₃ := by
    obtain ⟨k,e,hk⟩ := strictOld j 3 hlt hj
    have hk' : k.val<3 := hk
    exact ⟨⟨k.val,hk'⟩,e⟩
  have locate4 (j : Fin s) (hj : Dirty c w U j) (hlt : j < e) : j∈Set.range old₄ := by
    obtain ⟨k,e,hk⟩ := strictOld j 4 hlt hj
    have hk' : k.val<4 := hk
    exact ⟨⟨k.val,hk'⟩,e⟩
  have midDirty (j : Fin s) (h₁ : a < j) (h₂ : j < e) : ¬ Dirty c w U j := by
    intro dn
    obtain ⟨k,hk,hr⟩ := strictOld j 4 h₂ dn
    have hk' : (3:Fin 5)<k := mono.lt_iff_lt.mp (hk.symm ▸ h₁)
    have h₃ : 3<k.val := hk'
    have h₄ : k.val<4 := hr
    omega
  have au : a < u := by
    by_contra! he
    let S := Finset.univ.image old₃
    have hs : beforeDirty A w U u ⊆ S := by
      intro j hj
      obtain ⟨hl,hdi⟩ := mem_beforeDirty.mp hj
      obtain ⟨k,hk⟩ := locate3 j hdi (hl.trans_le he)
      exact Finset.mem_image.mpr ⟨k,Finset.mem_univ _,hk⟩
    have ht := (Finset.card_le_card hs).trans (Finset.card_image_le (s:=Finset.univ) (f:=old₃))
    simp only [Finset.card_univ,Fintype.card_fin] at ht
    have hcard := at_least_four_clean_donors h ha hu ufirst
    omega
  have before4 (j : Fin s) (hj : j < a) (hkept : Kept c w U j) : j∈Set.range old₃ := by
    rcases clean_or_dirty hkept with hcl|hdi
    · exact (ufirst j (hj.trans au) hcl).elim
    · exact locate3 j hdi hj
  obtain ⟨va,hva,vapre,Rva,a0⟩ := dirty_pivot_input h ha (k:=0) (by decide) old₃
    (mono.injective.comp (Fin.castLE_injective (by decide)))
    (fun j => dirty _) (dirty 3) (fun j => mono (show (Fin.castLE (by decide) j : Fin 5)<3 from j.isLt))
    (Or.inl before4)
  have mid_empty (j : Fin s) (h₁ : a < j) (h₂ : j < e) (h₃ : j < u) :
      ¬Kept c w U j := by
    intro hh
    rcases clean_or_dirty hh with hcl|hdi
    · exact ufirst j h₃ hcl
    · exact midDirty j h₁ h₂ hdi
  have aeTaps : B e e=0 ∧ B e a=0 ∧ (u < e → B e u=0) ∧
      (∀ j < e, Kept c w U j → Dirty c w U j ∨ j=u) := by
    by_cases eu : e < u
    · have cover (j : Fin s) (hj : j < e) (hh : Kept c w U j) : j∈Set.range old₄ := by
        rcases clean_or_dirty hh with hcl|hdi
        · exact (ufirst j (hj.trans eu) hcl).elim
        · exact locate4 j hdi hj
      obtain ⟨_,_,_,_,e0⟩ := dirty_pivot_input h ha (k:=1) (by decide) old₄
        (mono.injective.comp (Fin.castLE_injective (by decide)))
        (fun j => dirty _) (dirty 4) (fun j => mono (show (Fin.castLE (by decide) j : Fin 5)<4 from j.isLt))
        (Or.inl cover)
      have r0 : R e e=0 := by rw [commutatorMatrix_diagonal ha',e0,zero_pow (by decide),neg_zero]
      have rz : R e a=0 := by
        have er := selected_prefix_tap hr' ea vapre r0
          (fun j h₁ h₂ => Or.inl (commutatorMatrix_zero_col
            (fun _ => foldMatrix_zero_col (mid_empty j h₁ h₂ (h₂.trans eu))) e))
        rw [mulR _ Rva,eq_comm] at er
        exact (mul_eq_zero.mp er).resolve_right hva
      have er := commutatorMatrix_offdiag («c» := c) ha' e0 a0
        (fun j j1 j2 => Or.inl (foldMatrix_zero_col (mid_empty j j1 j2 (j2.trans eu))))
      rw [rz] at er
      have hn : c e-c a≠0 := sub_ne_zero.mpr (fun hc =>
        (ne_of_gt ea) (dirty_distinct h (dirty 4) (dirty 3) hc))
      exact ⟨e0,(mul_eq_zero.mp er.symm).resolve_left hn,
        fun he => (lt_asymm eu he).elim,fun j hje hk => by
          rcases clean_or_dirty hk with hcl|hdi
          · exact (ufirst j (hje.trans eu) hcl).elim
          · exact Or.inl hdi⟩
    · have ue : u < e := lt_of_le_of_ne (le_of_not_gt eu) (fun eq => by
        apply (dirty 4).2
        change w e=0
        rw [←eq]
        exact hu.2)
      obtain ⟨Pnv,u0⟩ := first_clean_nonroot h ha ho hp hu ufirst
      have preFour : beforeDirty A w U u = Finset.univ.image old₄ := by
        ext j
        constructor
        · intro hj
          obtain ⟨hju,hDirty⟩ := mem_beforeDirty.mp hj
          obtain ⟨k,e⟩ := locate4 j hDirty (hju.trans ue)
          exact Finset.mem_image.mpr ⟨k,Finset.mem_univ _,e⟩
        · intro hj
          obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hj
          have hka : old₄ k ≤ a := mono.monotone
            (show (Fin.castLE (by decide) k : Fin 5) ≤ 3 from by
              change k.val ≤ 3; have := k.isLt; omega)
          exact mem_beforeDirty.mpr ⟨hka.trans_lt au,dirty _⟩
      have cardFour : (beforeDirty A w U u).card=4 := by
        have he : Function.Injective old₄ :=
          mono.injective.comp (Fin.castLE_injective (by decide))
        rw [preFour,Finset.card_image_of_injective _ he]
        simp
      have uan : B u a≠0 := all_four_clean_taps h ha hu ufirst cardFour a
        (mem_beforeDirty.mpr ⟨au,dirty 3⟩)
      have rau : R u a=0 := by
        have r0 : R u u=0 := by rw [commutatorMatrix_diagonal ha',u0,zero_pow (by decide),neg_zero]
        have er := selected_prefix_tap hr' au vapre r0
          (fun j h₁ h₂ => Or.inl (commutatorMatrix_zero_col
            (fun _ => foldMatrix_zero_col (mid_empty j h₁ (h₂.trans ue) h₂)) u))
        rw [mulR _ Rva,eq_comm] at er
        exact (mul_eq_zero.mp er).resolve_right hva
      have c_eq : c u=c a := by
        have eq := commutatorMatrix_offdiag («c» := c) ha' u0 a0
          (fun j h₁ h₂ => Or.inl (foldMatrix_zero_col (mid_empty j h₁ (h₂.trans ue) h₂)))
        rw [rau] at eq
        exact sub_eq_zero.mp ((mul_eq_zero.mp eq.symm).resolve_right uan)
      have noLatter (j : Fin s) (h₁ : u < j) (h₂ : j < e) : ¬Clean c w U j := by
        intro hc
        obtain ⟨v,⟨uv,hv⟩,beforeV⟩ := exists_first_of («R» := fun j => u < j ∧ Clean c w U j)
          ⟨j,h₁,hc⟩
        have ve : v < e := by
          by_contra! h
          exact beforeV j (h₂.trans_le h) ⟨h₁,hc⟩
        have cuv : c v≠c u := fun eq => (ne_of_gt uv) (clean_distinct hv hu eq)
        obtain ⟨f,hd,hf0,hfu,hju,hfv,hjv⟩ := second_clean_test (c u) (c v)
          (clean_clock hv) cuv
        obtain ⟨q,hq,fit⟩ := fit_four_donors h ha hu ufirst cardFour f hd hf0 hfu hju
        let y := evalNodes A f+(fun i => q.eval (c i)*w i)
        have ht : OrdinaryTrace A 5 y f := head_trace h (k:=2) (by decide) f q hd hq
        have out := fold_clean_value h (n:=5) (by decide) (by decide) ht hf0 hv
        apply hjv
        rw [←out]
        apply row_zero_from_taps
        intro i
        by_cases iv : v < i
        · exact Or.inl (ha' _ _ iv)
        by_cases hi : Kept c w U i
        · refine Or.inr ?_
          rw [restrict_apply,ite_eq_left hi]
          rcases clean_or_dirty hi with hcl|hdi
          · have euv : i=u ∨ i=v := by
              rcases lt_trichotomy i u with ib|rfl|ib
              · exact (ufirst i ib hcl).elim
              · exact Or.inl rfl
              · rcases lt_or_eq_of_le (le_of_not_gt iv) with ic|rfl
                · exact (beforeV i ic ⟨ib,hcl⟩).elim
                · exact Or.inr rfl
            rcases euv with rfl|rfl
            · simp [y,hfu,hcl.2]
            · simp [y,hfv,hcl.2]
          · have iy : i<u := by
              by_contra! he
              rcases lt_or_eq_of_le he with he|rfl
              · exact midDirty i (au.trans he) ((le_of_not_gt iv).trans_lt ve) hdi
              · exact hdi.2 hu.2
            exact fit i (mem_beforeDirty.mpr ⟨iy,hdi⟩)
        · exact Or.inl (foldMatrix_zero_col hi)
      have keepOnly (j : Fin s) (hj : j < e) (hkept : Kept c w U j) :
          Dirty c w U j ∨ j=u := by
        rcases clean_or_dirty hkept with hcl|hdi
        · rcases lt_trichotomy j u with hh|rfl|hh
          · exact (ufirst _ hh hcl).elim
          · exact Or.inr rfl
          · exact (noLatter _ hh hj hcl).elim
        · exact Or.inl hdi
      have cover (j : Fin s) (hj : j < e) (hk : Kept c w U j) :
          j∈Set.range old₄ ∨ j=u :=
        (keepOnly j hj hk).imp (fun hdi => locate4 j hdi hj) id
      obtain ⟨_,_,_,_,e0⟩ := dirty_pivot_input h ha (k:=1) (by decide) old₄
        (mono.injective.comp (Fin.castLE_injective (by decide)))
        (fun j => dirty _) (dirty 4) (fun j => mono (show (Fin.castLE (by decide) j : Fin 5)<4 from j.isLt))
        (Or.inr ⟨rfl,u,ue,hu,Pnv,cover⟩)
      obtain ⟨θ,hθ,hval⟩ := clean_contrast h
      let x := diag c θ
      have xpre (j : Fin s) (hj : j < u) : D x j=0 := by
        by_cases hk : Kept c w U j
        · rcases clean_or_dirty hk with hcl|hdi
          · exact (ufirst _ hj hcl).elim
          · simp [x,restrict_apply,hdi.1,hval j,hdi.2]
        · simp [restrict_apply,hk]
      have xnz : D x u≠0 := by
        rw [restrict_apply,ite_eq_left hu.1]
        simp only [x,diag_apply,hval u,hu.1.1.1,hu.2,ne_eq,not_true_eq_false,or_self,ite_false]
        exact mul_ne_zero (clean_clock hu) Pnv
      have Rx : mat R (D x)=0 := by
        rw [mat_commutatorMatrix]
        apply reduced_commutator_zero h (k:=1) (by decide) hθ.clock (by simp) old₄
          (mono.injective.comp (Fin.castLE_injective (by decide))) (by decide) (fun j => dirty _)
        intro j
        rw [←mat_commutatorMatrix]
        have hja : old₄ j ≤ a := mono.monotone
          (show (Fin.castLE (by decide) j : Fin 5) ≤ 3 from by
            change j.val ≤ 3; have := j.isLt; omega)
        exact mat_zero_before hr' xpre _ (hja.trans_lt au)
      have r0 : R e e=0 := by rw [commutatorMatrix_diagonal ha',e0,zero_pow (by decide),neg_zero]
      have midU (j : Fin s) (h₁ : u < j) (h₂ : j < e) : ¬Kept c w U j := by
        intro hk
        rcases clean_or_dirty hk with hcl|hdi
        · exact noLatter j h₁ h₂ hcl
        · exact midDirty j (au.trans h₁) h₂ hdi
      have euR : R e u=0 := by
        have q := selected_prefix_tap hr' ue xpre r0 (fun j j1 j2 =>
          Or.inl (commutatorMatrix_zero_col (fun _ => foldMatrix_zero_col (midU j j1 j2)) e))
        rw [mulR _ Rx,eq_comm] at q
        exact (mul_eq_zero.mp q).resolve_right xnz
      have cne : c e-c u≠0 := by
        rw [c_eq]
        exact sub_ne_zero.mpr (fun hc => (ne_of_gt ea)
          (dirty_distinct h (dirty 4) (dirty 3) hc))
      have B_eu : B e u=0 := by
        have eq := commutatorMatrix_offdiag («c» := c) ha' e0 u0
          (fun j j1 j2 => Or.inl (foldMatrix_zero_col (midU j j1 j2)))
        rw [euR] at eq
        exact (mul_eq_zero.mp eq.symm).resolve_left cne
      have midA (j : Fin s) (h₁ : a < j) (h₂ : j < e) : B e j=0 := by
        by_cases hk : Kept c w U j
        · rcases keepOnly j h₂ hk with hdi|rfl
          · exact (midDirty _ h₁ h₂ hdi).elim
          · exact B_eu
        · exact foldMatrix_zero_col hk
      have eaR : R e a=0 := by
        have rmid (j : Fin s) (h₁ : a < j) (h₂ : j < e) : R e j=0 := by
          by_cases hk : Kept c w U j
          · rcases keepOnly _ h₂ hk with hdi|rfl
            · exact (midDirty _ h₁ h₂ hdi).elim
            · exact euR
          · exact commutatorMatrix_zero_col (fun _ => foldMatrix_zero_col hk) e
        have eq := selected_prefix_tap hr' ea vapre r0 (fun j j1 j2 => Or.inl (rmid _ j1 j2))
        rw [mulR _ Rva,eq_comm] at eq
        exact (mul_eq_zero.mp eq).resolve_right hva
      have eq := commutatorMatrix_offdiag («c» := c) ha' e0 a0 (fun j j1 j2 => Or.inl (midA _ j1 j2))
      rw [eaR] at eq
      have cne' : c e-c a≠0 := by simpa only [c_eq] using cne
      exact ⟨e0,(mul_eq_zero.mp eq.symm).resolve_left cne',fun _ => B_eu,keepOnly⟩
  obtain ⟨e0,ae0,eu0,cover⟩ := aeTaps
  refine ⟨d,mono,dirty,fun i j hnot => ?_⟩
  by_cases later : d i<j
  · exact ha' _ _ later
  by_cases hk : Kept c w U j
  · have jle : j ≤ d i := le_of_not_gt later
    have ie : d i ≤ e := mono.monotone (by change i.val ≤ 4; have := i.isLt; omega)
    rcases lt_or_eq_of_le (jle.trans ie) with jl|rfl
    · rcases cover j jl hk with hj|rfl
      · obtain ⟨k,equal,kl⟩ := strictOld j 4 jl hj
        by_cases k3 : k.val<3
        · exact (hnot ⟨k.val,k3⟩ equal.symm).elim
        · have e3 : k=3 := Fin.ext (by change k.val<4 at kl; omega)
          subst k
          have iya : a ≤ d i := by
            change d 3 ≤ d i
            rwa [equal]
          have ii : (3:Fin 5) ≤ i := mono.le_iff_le.mp iya
          rcases (show i=3 ∨ i=4 by
            have hi := i.isLt
            change 3 ≤ i.val at ii
            rcases (show i.val=3 ∨ i.val=4 by omega) with h|h
            · exact Or.inl (Fin.ext h)
            · exact Or.inr (Fin.ext h)) with rfl|rfl
          · simpa only [←equal] using a0
          · simpa only [←equal] using ae0
      · have i4 : i=4 := by
          apply Fin.ext
          have hi := i.isLt
          by_contra hne
          have hle : i ≤ (3:Fin 5) := by change i.val ≤ 3; omega
          exact (not_le_of_gt au) (jle.trans (mono.monotone hle))
        subst i
        exact eu0 jl
    · have ieq : d i=e := le_antisymm ie jle
      rw [ieq]
      exact e0
  · exact foldMatrix_zero_col hk

theorem no_grade3_head (h : Grade3Head A U w P) (ha : LowerArray A)
    (ho : HasTreeOrderAtLeast A b p) (hp : 8 ≤ p) : False := by
  obtain ⟨d,mono,dirty,common⟩ := common_first_three h ha ho hp
  let z : Fin 5 → K := fun i => c (d i)
  have hz : Function.Injective z := fun i j e =>
    mono.injective (dirty_distinct h (dirty i) (dirty j) e)
  apply five_dirty_origin_jets z hz P h.degree h.constant_ne
  · intro i
    rw [←h.fits _ (dirty i).2]
    exact (dirty i).2
  · intro f q hf hf0 hq hh
    let v := evalNodes A f+(fun i => q.eval (c i)*w i)
    have ht : OrdinaryTrace A 4 v f := head_trace h (k:=1) (by decide) f q hf hq
    have hv0 (i : Fin 3) : D v (d (Fin.castLE (by decide) i))=0 := by
      let j := (Fin.castLE (by decide) i : Fin 5)
      have e : D v (d j)=f.eval (z j)+P.eval (z j)*q.eval (z j) := by
        rw [restrict_apply,ite_eq_left (dirty j).1]
        change f.eval (c (d j))+q.eval (c (d j))*w (d j)=_
        rw [h.fits _ (dirty j).2]
        dsimp [z]
        ring
      exact e.trans (hh i)
    obtain ⟨y,hy,e⟩ := fold_primitive h (by decide) (by decide) ht hf0
    have A0 (i : Fin 5) : y (d i)=0 := by
      have ew : mat B (D v) (d i)=0 := by
        apply row_zero_from_taps
        intro l
        by_cases hl : ∃ j : Fin 3,l=d (Fin.castLE (by decide) j)
        · obtain ⟨j,rfl⟩ := hl
          exact Or.inr (hv0 j)
        · exact Or.inl (common i l (fun k he => hl ⟨k,he⟩))
      have h := (congrFun e (d i)).symm.trans ew
      rwa [restrict_apply,ite_eq_left (dirty i).1] at h
    have pure := hy.pure
    have hb : zeroSpace A 5=chain (diag c) U w 3 := h.band 2 (by decide)
    rw [hb] at pure
    obtain ⟨u,hu,Q,hdeg,hex⟩ := exists_head_poly pure
    have hd : Q.natDegree ≤ 2 := by
      by_cases hQ : Q=0
      · simp [hQ]
      · have h := (natDegree_lt_iff_degree_lt hQ).mpr hdeg
        omega
    refine ⟨-Q,by simpa using hd,fun i => ?_⟩
    have hui : u (d i)=0 := by
      by_contra he
      exact (dirty i).1.1.1 ⟨u,hu,he⟩
    have hh := hex (d i)
    simp only [Pi.sub_apply,A0 i,evalNodes_apply,hui,zero_add,zero_sub] at hh
    rw [h.fits _ (dirty i).2] at hh
    change (formalPrimitive f).eval (c (d i))=P.eval (c (d i))*(-Q).eval (c (d i))
    rw [eval_neg,←neg_mul_eq_mul_neg,mul_comm,←hh,neg_neg]

end
end RKCert.Paired.Reduce
