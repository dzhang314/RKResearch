module

public import RKCert.ReviewedNative.DIRKCubicCleanDonors
public import RKCert.ReviewedNative.DIRKC2GradeSixHead

@[expose] public section

/-! # Native C(2) cubic-head chronological obstruction

Fixing the actual zero first row retains the blank signature at the
origin, before every dirty pivot. The only possible intervening nonzero
clean signature is moved past by two exact Volterra tap eliminations.
-/
namespace RKResearch.Certified.Graded.HeadFiber

open Polynomial RKCert.OneEscape Signature
open scoped Matrix Classical
variable {K : Type*} [Field K] [CharZero K] {s p : ℕ}
variable {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : Fin (s+1) → K}

omit [CharZero K] in
private theorem pivot_tap_zero
    {M : Matrix (Fin (s+1)) (Fin (s+1)) K} (ha : M.IsLowerTriangular)
    {i j : Fin (s+1)} (ji : j < i) (di : M i i=0) (dj : M j j=0)
    (v : Fin (s+1) → K) (pre : ∀ k < j, v k=0) (nv : v j≠0)
    (vol : mat (volterraTaps M) v=0)
    (mid : ∀ k, j < k → k < i → M i k=0 ∧ volterraTaps M i k=0) :
    volterraTaps M i j=0 ∧ (nodes M i-nodes M j)*M i j=0 := by
  have rz : volterraTaps M i i=0 := by
    rw [taps_of_zero_diags ha di di (fun _ h g => False.elim ((lt_asymm h) g)),sub_self,zero_mul]
  have eq := mat_single_tap (volterraTaps M) v i j (fun k kn => by
    rcases lt_or_gt_of_ne kn with lo|hi
    · rw [pre _ lo,mul_zero]
    · rcases lt_trichotomy k i with ki|rfl|ik
      · rw [(mid k hi ki).2,zero_mul]
      · rw [rz,zero_mul]
      · rw [taps_lower ha ik,zero_mul])
  have e : volterraTaps M i j=0 := by
    have z := congrFun vol i
    rw [eq,Pi.zero_apply] at z
    exact (mul_eq_zero.mp z).resolve_right nv
  exact ⟨e, (taps_of_zero_diags ha di dj (fun k lo hi => by rw [(mid k lo hi).1,zero_mul])).symm ▸ e⟩

local notation "c" => nodes A
local notation "w" => monomialStageDefect A 2
local notation "B" => fold A w
local notation "R" => volterraTaps B

set_option maxHeartbeats 1400000 in
/-- The isolated physical C(2) cubic-head profile is impossible.
The order hypothesis is used at most through the paid order-eight
clean-clock detection; all row eliminations are finite triangular identities. -/
theorem dirk_C2_no_cubic_head (ha : A.IsLowerTriangular) (ho : HasOrder p A b) (pay : 8≤p)
    (c₂ : monomialStageDefect A 1=0)
    (P : K[X]) (nz : P≠0) (deg : P.natDegree≤3)
    (many : 4<(physicalSites (nodes A) (monomialStageDefect A 2)).card)
    (fit : ∀ i, monomialStageDefect A 2 i≠0 → monomialStageDefect A 2 i=P.eval (nodes A i))
    (band : ∀ k≤3, zeroSpace A (3+k)=chain (diag (nodes A)) ⊥ (monomialStageDefect A 2) (1+k)) :
    False := by
  classical
  have lb : (B).IsLowerTriangular := fold_lower ha
  have P0 := cubic_amplitude_nonzero_at_origin ha ho (by omega) band P nz deg fit
  have zrow := dirk_first_row_of_zero_quadratic ha (congrFun c₂ 0)
  have c0 : c 0=0 := by simp [nodes,Matrix.mulVec,dotProduct,zrow]
  have w0 : w 0=0 := zeroSpace_at_zero_row zrow 3 (monomialStageDefect_mem A 2)
  obtain ⟨u,wu,cu,Pu,ud,cleanBefore,_,_⟩ := dirk_C2_first_clean_clock ha ho pay c₂ band P nz deg fit
  change w u=0 at wu
  change c u≠0 at cu
  change P.eval (c u)≠0 at Pu
  have uRep : first c w u=u := first_of_no_earlier (fun j hj eq => by
    have jz : w j=0 := (congrArg Prod.snd eq).trans wu
    have jc : c j=c u := congrArg Prod.fst eq
    exact cu (jc.symm.trans (cleanBefore j hj jz)))
  have u0 : B u u=0 := (fold_diag_of_first ha u uRep).trans ud
  have blank (j : Fin (s+1)) (rep : first c w j=j) (wj : w j=0) (cj : c j=0) : j=0 := by
    have r0 : first c w 0=0 := le_antisymm (first_le c w 0) (Fin.zero_le _)
    refine rep.symm.trans ((first_congr ?_).trans r0)
    exact Prod.ext (cj.trans c0.symm) (wj.trans w0.symm)
  obtain ⟨d,mono,inj,dirty,early⟩ := first_five_dirty (A:=A) P fit many
  let a := d 3
  let e := d 4
  let D (k : Fin 5) : Fin k.val → Fin (s+1) := fun l => d (Fin.castLE k.isLt.le l)
  have Dc (k : Fin 5) : Function.Injective (fun l => c (D k l)) :=
    inj.comp (Fin.castLE_injective k.isLt.le)
  have Dd (k : Fin 5) (l : Fin k.val) : w (D k l)≠0 := (dirty _).2
  have Dpre (k : Fin 5) (l : Fin k.val) : D k l < d k := mono (show _ < k from l.isLt)
  have Dnew (k : Fin 5) (l : Fin k.val) : c (D k l)≠c (d k) := fun eq =>
    (ne_of_lt (Dpre k l)) (congrArg d (inj eq))
  have older (k : Fin 5) (j : Fin (s+1)) (jp : j < d k) (jw : w j≠0) :
      ∃ l : Fin k.val, D k l=first c w j := by
    let r := first c w j
    have wr : w r=w j := congrArg Prod.snd (first_signature c w j)
    have rj : r < d k := (first_le c w j).trans_lt jp
    have wn : w r≠0 := by rwa [wr]
    obtain ⟨l,eq,h⟩ := early r (first_idempotent c w j) wn k rj.le
    have hl : l < k := mono.lt_iff_lt.mp (eq.symm ▸ rj)
    exact ⟨⟨l.val,hl⟩,eq⟩
  have atOlder (k : Fin 5) (j : Fin (s+1)) (jp : j < d k) (jw : w j≠0) :
      ∃ l : Fin k.val, c (D k l)=c j := by
    obtain ⟨l,h⟩ := older k j jp jw
    exact ⟨l,h ▸ (congrArg Prod.fst (first_signature c w j))⟩
  let S : Finset (Fin (s+1)) := Finset.univ.image (D 3)
  have S3 : S.card≤3 := by
    have ch := Finset.card_image_le (s:=Finset.univ) (f:=D 3)
    simpa [S] using ch
  have Sinj : Set.InjOn c S := by
    intro i hi j hj eq
    obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hj
    exact congrArg (D 3) (Dc 3 eq)
  have loc3 (j) (h : j < a) (wj : w j≠0) (rep : first c w j=j) : j∈S := by
    obtain ⟨l,e⟩ := older 3 j h wj
    exact Finset.mem_image.mpr ⟨l,Finset.mem_univ _,e.trans rep⟩
  have au : a < u := by
    by_contra! h
    apply first_clean_taps_not_three ha c₂ band wu cu u0 cleanBefore S S3 Sinj
    intro j ju jw nb
    have rep : first c w j=j := by_contra fun nr => nb (fold_zero_nonfirst u j nr)
    exact loc3 j (ju.trans_le h) jw rep
  have ae : a < e := mono (by decide)
  have loc4 (j : Fin (s+1)) (je : j < e) (jw : w j≠0) (rep : first c w j=j) :
      j∈S ∨ j=a := by
    obtain ⟨l,eq,_⟩ := early j rep jw 4 je.le
    have l4 : l < (4:Fin 5) := mono.lt_iff_lt.mp (eq.symm ▸ je)
    by_cases l3 : l.val<3
    · exact Or.inl (Finset.mem_image.mpr ⟨⟨l.val,l3⟩,Finset.mem_univ _,eq⟩)
    · exact Or.inr (eq.symm.trans (congrArg d (Fin.ext (by have : l.val<4 := l4; omega))))
  have gap (j : Fin (s+1)) (aj : a < j) (je : j < e) (rep : first c w j=j) (wj : w j≠0) : False := by
    rcases loc4 j je wj rep with old|eq
    · obtain ⟨l,_,h⟩ := Finset.mem_image.mp old
      exact (not_lt_of_gt aj) (h ▸ Dpre 3 l)
    · exact (ne_of_gt aj) eq
  obtain ⟨f,q,df,_,dq,pa,preA,va,aDiag⟩ :=
    dirty_pivot_test ha ho band P deg P0 fit (k:=0) (by decide) (by omega)
      (dirty 3).2 (D 3) (Dpre 3) (Dc 3) (Dd 3) (Dnew 3) (atOlder 3)
      (Or.inl (fun j ja => cleanBefore j (ja.trans au)))
  let x := headInput A w f q
  have a0 : B a a=0 := (fold_diag_of_first ha a (dirty 3).1).trans aDiag
  have Rx : mat R x=0 := by
    rw [mat_taps,fold_volterra_headInput (band 0 (by decide)) (band 1 (by decide)) df dq,va]
  have cleanClass (j) (ju : j < u) (wj : w j=0) : c j=0 := cleanBefore j ju wj
  have blocksBefore (j) (ja : a < j) (ju : j < u) (je : j < e) :
      first c w j≠j := by
    intro rep
    by_cases n : w j=0
    · exact (ne_of_gt (Fin.zero_le a |>.trans_lt ja)) (blank j rep n (cleanClass j ju n))
    · exact gap j ja je rep n
  have runLast (H : (∀ j < e, w j=0 → c j=0) ∨
      (1=1 ∧ ∃ z : K, z≠0 ∧ P.eval z≠0 ∧ ∀ j < e, w j=0 → c j≠0 → c j=z)) :
      B e e=0 := by
    obtain ⟨_,_,_,_,_,_,_,_,db⟩ := dirty_pivot_test ha ho band P deg P0 fit (k:=1) (by decide) (by omega)
      (dirty 4).2 (D 4) (Dpre 4) (Dc 4) (Dd 4) (Dnew 4) (atOlder 4) H
    exact (fold_diag_of_first ha e (dirty 4).1).trans db
  obtain ⟨e0,ea0,cleanGone⟩ : B e e=0 ∧ B e a=0 ∧
      (∀ j < e, first c w j=j → w j=0 → c j≠0 → B e j=0) := by
    have en : e≠u := by
      intro eq
      have h : w e=0 := by rw [eq,wu]
      exact (dirty 4).2 h
    rcases lt_or_gt_of_ne en with eu|ue
    · have e0 := runLast (Or.inl fun j je => cleanClass j (je.trans eu))
      have ⟨_,tap⟩ := pivot_tap_zero lb ae e0 a0 x preA pa Rx (fun j ja je => by
        have h := fold_zero_nonfirst (A:=A) e j (blocksBefore j ja (je.trans eu) je)
        exact ⟨h,taps_zero_col (fun i => fold_zero_nonfirst i j (blocksBefore j ja (je.trans eu) je)) e⟩)
      rw [fold_nodes] at tap
      exact ⟨e0,(mul_eq_zero.mp tap).resolve_left (sub_ne_zero.mpr (fun z=> (by decide : (4:Fin 5)≠3) (inj z))),
        fun j je _ wj cj => (cj (cleanClass j (je.trans eu) wj)).elim⟩
    · have live : B u a≠0 := by
        intro az
        apply first_clean_taps_not_three ha c₂ band wu cu u0 cleanBefore S S3 Sinj
        intro j ju jw nb
        have rep : first c w j=j := by_contra fun nr => nb (fold_zero_nonfirst u j nr)
        rcases loc4 j (ju.trans ue) jw rep with old|rfl
        · exact old
        · exact (nb az).elim
      have ⟨_,tap⟩ := pivot_tap_zero lb au u0 a0 x preA pa Rx (fun j ja ju => by
        have bad := blocksBefore j ja ju (ju.trans ue)
        exact ⟨fold_zero_nonfirst u j bad,taps_zero_col (fun i => fold_zero_nonfirst i j bad) u⟩)
      rw [fold_nodes] at tap
      have uClock : c u=c a := sub_eq_zero.mp ((mul_eq_zero.mp tap).resolve_right live)
      have noNext (j : Fin (s+1)) (uj : u < j) (je : j < e) (rep : first c w j=j) (jw : w j=0) (jc : c j≠0) : False := by
        let S' : Finset (Fin (s+1)) := Finset.univ.filter
          (fun v => u < v ∧ v < e ∧ first c w v=v ∧ w v=0 ∧ c v≠0)
        have mem : j∈S' := Finset.mem_filter.mpr ⟨Finset.mem_univ _,uj,je,rep,jw,jc⟩
        let v := S'.min' ⟨j,mem⟩
        obtain ⟨uv,ve,vr,vw,vc⟩ := (Finset.mem_filter.mp (S'.min'_mem ⟨j,mem⟩)).2
        have different : c v≠c u := by
          intro eq
          have both : (c v,w v)=(c u,w u) := Prod.ext eq (vw.trans wu.symm)
          have equal := first_congr both
          have vrep : first c w v=v := vr
          rw [vrep,uRep] at equal
          exact (ne_of_gt uv) equal
        obtain ⟨g,dg,g0,gu,gv,Ju,Jv⟩ := two_clock_separating_primitive (c u) (c v) vc different
        obtain ⟨Q,dQ,zeros⟩ := fit_three_donors (A:=A) (D 3) (Dc 3) (Dd 3) g
        let z := headInput A w g Q
        have mute (k : Fin (s+1)) (h : k∈S) : z k=0 := by
          obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp h
          exact zeros l
        have zU : mat B z u=0 := (fold_clean_primitive band (k:=2) (by decide) (by omega) dQ wu).trans Ju
        have zA : z a=0 := by
          have single := mat_single_tap B z u a (fun k ne => by
            rcases lt_trichotomy k u with ku|rfl|uk
            · by_cases rep : first c w k=k
              · by_cases k0 : w k=0
                · rw [show z k=g.eval (c k)+Q.eval (c k)*w k from headInput_apply A w g Q k,
                    k0,cleanBefore k ku k0,g0,mul_zero,add_zero,mul_zero]
                · exact (loc4 k (ku.trans ue) k0 rep).elim (fun h=>by rw [mute _ h,mul_zero])
                    (fun h=>False.elim (ne h))
              · rw [fold_zero_nonfirst u k rep,zero_mul]
            · rw [u0,zero_mul]
            · rw [lb uk,zero_mul])
          rw [zU] at single
          exact (mul_eq_zero.mp single.symm).resolve_left live
        apply Jv
        rw [← fold_clean_primitive band (k:=2) (by decide) (by omega) dQ vw]
        change mat B z v=0
        rw [mat_apply,Matrix.mulVec_apply_eq_sum]
        apply Finset.sum_eq_zero
        intro k _
        rcases lt_trichotomy k v with kv|rfl|vk
        · by_cases rep : first c w k=k
          · by_cases kn : w k=0
            · by_cases ck : c k=0
              · simp [z,kn,ck,g0]
              have eq : k=u := by
                rcases lt_trichotomy k u with ku|eq|uk
                · exact (ck (cleanBefore k ku kn)).elim
                · exact eq
                · exact False.elim ((not_le_of_gt kv) (S'.min'_le k
                    (Finset.mem_filter.mpr ⟨Finset.mem_univ _,uk,kv.trans ve,rep,kn,ck⟩)))
              subst k
              simp [z,wu,gu]
            · exact (loc4 k (kv.trans ve) kn rep).elim (fun h=>by rw [mute _ h,mul_zero])
                (fun h=>by rw [h,zA,mul_zero])
          · rw [fold_zero_nonfirst v k rep,zero_mul]
        · have wv : w v=0 := vw
          have e : z v=0 := by simp [z,wv,gv]
          rw [e,mul_zero]
        · have e : B v k=0 := lb vk
          rw [e,zero_mul]
      have oldClean (j : Fin (s+1)) (je : j < e) (wj : w j=0) (cj : c j≠0)
          (rep : first c w j=j) : j=u := by
        rcases lt_trichotomy j u with ju|eq|uj
        · exact (cj (cleanClass j ju wj)).elim
        · exact eq
        · exact (noNext j uj je rep wj cj).elim
      have allClean (j : Fin (s+1)) (je : j < e) (wj : w j=0) (cj : c j≠0) : c j=c u := by
        let j' := first c w j
        have hj : c j'=c j := congrArg Prod.fst (first_signature c w j)
        have hr : w j'=w j := congrArg Prod.snd (first_signature c w j)
        have eq := oldClean j' ((first_le c w j).trans_lt je) (hr.trans wj) (fun z=>cj (hj.symm.trans z))
          (first_idempotent c w j)
        exact hj.symm.trans (congrArg c eq)
      have e0 := runLast (Or.inr ⟨rfl,c u,cu,Pu,allClean⟩)
      let y := headInput A w (X*P) (-X)
      have yval (j : Fin (s+1)) : y j=c j*(P.eval (c j)-w j) := by
        simp only [y,headInput_apply,eval_mul,eval_X,eval_neg]
        ring
      have yn : y u≠0 := by rw [yval,wu,sub_zero]; exact mul_ne_zero cu Pu
      have yp (j : Fin (s+1)) (ju : j < u) : y j=0 := by
        by_cases n : w j=0
        · rw [yval,cleanClass j ju n,zero_mul]
        · rw [yval,show w j=P.eval (c j) from fit j n,sub_self,mul_zero]
      have ydeg : (X*P).natDegree≤4 := natDegree_mul_le.trans (by rw [natDegree_X]; omega)
      have QE : (-X:K[X]).natDegree≤1 := by simp
      have VY := paid_volterra_zero ho (k:=1) (by omega) band (by decide) ydeg QE
        (D 4) (Dc 4) (Dd 4) (fun j => by
          have du : D 4 j < u := (mono.monotone (show (Fin.castLE (by decide : 4≤5) j : Fin 5)≤3 by
            change j.val ≤ 3; have := j.isLt; omega)).trans_lt au
          rw [volterra_pivot ha _ _ (fun l ll => yp l (ll.trans du)),yp _ du,mul_zero])
      have RY : mat R y=0 := by
        rw [mat_taps,fold_volterra_headInput (band 1 (by decide)) (band 2 (by decide)) ydeg QE,VY]
      have absent (j) (aj : a < j) (je : j < e) (nu : j≠u) : first c w j≠j := by
        intro r
        by_cases h : w j=0
        · by_cases d0 : c j=0
          · exact (ne_of_gt ((Fin.zero_le a).trans_lt aj)) (blank j r h d0)
          · exact nu (oldClean j je h d0 r)
        · exact gap j aj je r h
      have ⟨Reu,euTap⟩ := pivot_tap_zero lb ue e0 u0 y yp yn RY (fun j uj je => by
        have n := absent j (au.trans uj) je (ne_of_gt uj)
        exact ⟨fold_zero_nonfirst e j n,taps_zero_col (fun i => fold_zero_nonfirst i j n) e⟩)
      rw [fold_nodes,uClock] at euTap
      have diff : c e-c a≠0 := sub_ne_zero.mpr fun h => (by decide : (4:Fin 5)≠3) (inj h)
      have Beu := (mul_eq_zero.mp euTap).resolve_left diff
      have ⟨_,eaTap⟩ := pivot_tap_zero lb ae e0 a0 x preA pa Rx (fun j aj je => by
        by_cases hj : j=u
        · subst j
          exact ⟨Beu,Reu⟩
        · have n := absent j aj je hj
          exact ⟨fold_zero_nonfirst e j n,taps_zero_col (fun i => fold_zero_nonfirst i j n) e⟩)
      rw [fold_nodes] at eaTap
      refine ⟨e0,(mul_eq_zero.mp eaTap).resolve_left diff,fun j je jr jw jc => ?_⟩
      exact (oldClean j je jw jc jr).symm ▸ Beu
  apply five_dirty_three_donor_impossible band d inj (fun i => (dirty i).2) (D 3) (Dc 3) (Dd 3)
  intro g Q _ g0 _ zero i
  rw [←fold_mat_headInput,mat_apply,Matrix.mulVec_apply_eq_sum]
  apply Finset.sum_eq_zero
  intro j _
  by_cases later : d i < j
  · rw [lb later,zero_mul]
  have ji : j≤d i := le_of_not_gt later
  have di : d i≤e := mono.monotone (Fin.le_last i)
  by_cases rep : first c w j=j
  · rcases lt_or_eq_of_le (ji.trans di) with je|rfl
    · by_cases jw : w j=0
      · by_cases jc : c j=0
        · simp [jw,g0,jc]
        · have eq : i=4 := by
            by_contra ne
            have il : i ≤ (3:Fin 5) := by change i.val ≤ 3; have h := i.isLt; exact by omega
            exact jc (cleanBefore j ((ji.trans (mono.monotone il)).trans_lt au) jw)
          subst i; rw [cleanGone j je rep jw jc,zero_mul]
      · rcases loc4 j je jw rep with h|rfl
        · obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp h
          rw [zero l,mul_zero]
        · have il : (3:Fin 5) ≤ i := mono.le_iff_le.mp ji
          rcases (show i=3 ∨ i=4 by
            have h : 3 ≤ i.val := il
            have h' := i.isLt
            rcases (show i.val=3 ∨ i.val=4 by omega) with a|b
            · exact Or.inl (Fin.ext a)
            · exact Or.inr (Fin.ext b)) with rfl|rfl
          · rw [a0,zero_mul]
          · rw [ea0,zero_mul]
    · have ei : d i=e := le_antisymm di ji
      rw [ei,e0,zero_mul]
  · rw [fold_zero_nonfirst _ _ rep,zero_mul]

end RKResearch.Certified.Graded.HeadFiber

namespace RKResearch.Certified.Graded

/-- The true grade-six surplus in the non-invariant C(2) branch.
The invariant-grade-three fourth-entry branch is separate. -/
theorem dirk_grade_six_surplus_of_C2_of_grade_three_escape
    {K : Type*} [Field K] [CharZero K] {s p : ℕ} {A : Matrix (Fin s) (Fin s) K}
    {b : Fin s → K} (ha : A.IsLowerTriangular) (ho : HasOrder p A b) (pay : 8≤p)
    (c₂ : monomialStageDefect A 1=0)
    (escape : ¬ (zeroSpace A 3).map (diag (nodes A))≤zeroSpace A 3) :
    Module.finrank K (zeroSpace A 3)+4≤Module.finrank K (zeroSpace A 6) := by
  by_contra bad
  obtain ⟨P,nz,deg,many,fit,band⟩ := dirk_grade_six_C2_early_cubic_profile ha ho (by omega) c₂ bad escape
  cases s with
  | zero =>
    have lo := (dirk_grade_three_of_C2 ha ho (by omega) c₂).2
    have cap := Submodule.finrank_le (zeroSpace A 3)
    rw [Module.finrank_fin_fun] at cap
    omega
  | succ s => exact HeadFiber.dirk_C2_no_cubic_head ha ho pay c₂ P nz deg many fit band

end RKResearch.Certified.Graded
