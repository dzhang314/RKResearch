module

public import RKCert.ReviewedNative.ERKOrder16WeakFourRankRefund
public import RKCert.ReviewedNative.ERKOrder16WeakFourFivePlusOne
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace RKResearch.Certified.ERK16

open RKResearch Module Polynomial RKCert.Endpoint RKCert.Endpoint.WeightedClock
open RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse
open RKResearch.Certified.Graded.Reverse.Thin
open scoped BigOperators Classical Matrix

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A : Matrix (Fin 24) (Fin 24) K} {b w : Fin 24→K}
variable {U : Submodule K (Fin 24→K)} {Q P : K[X]}

private def compensated (b : Fin 24→K) (t i : Fin 24) : Fin 24→K :=
  coordinate (K:=K) i-(b i/b t) • coordinate (K:=K) t

private theorem compensated_apply (b : Fin 24→K) (t j i : Fin 24) :
    compensated b t j i=(if i=j then 1 else 0)-(b j/b t)*(if i=t then 1 else 0) := by
  simp [compensated,coordinate,Pi.single_apply,eq_comm]

/-- A blind coordinate goes outside any rank-three subspace of the
four-dimensional compensated carrier. No clock separation inside the
blind carrier is used. -/
private theorem compensated_escape {c d : Fin 24→K} {o t : Fin 24}
    (bt : b t≠0) (hU : U≤Hidden.carrier c b d o t)
    (rU : finrank K U=3) (rH : finrank K (Hidden.carrier c b d o t)=4) :
    ∃ j∈Hidden.blindRows c b d o t,
      Hidden.carrier c b d o t=U ⊔ K ∙ compensated b t j := by
  classical
  let G := Hidden.blindRows c b d o t
  let H := Hidden.carrier c b d o t
  have ht : t∉G := fun h=>((Hidden.mem_blindRows t).mp h).2.1 rfl
  have inCarrier (j : Fin 24) (hj : j∈G) : compensated b t j∈H := by
    apply Hidden.mem_ambientHidden.mpr
    refine ⟨?_,?_⟩
    · intro i hi it
      have ij : i≠j := fun e=>hi (e.symm ▸ hj)
      simp [compensated_apply,ij,it]
    · rw [compensated,map_sub,map_smul,smul_eq_mul,row_coordinate,row_coordinate,
        div_mul_cancel₀ _ bt,sub_self]
  have zero_of_restrict {u : Fin 24→K} (hu : u∈H) (zero : ∀ j∈G,u j=0) : u=0 := by
    have off (i : Fin 24) (it : i≠t) : u i=0 := by
      by_cases hi : i∈G
      · exact zero i hi
      · exact (Hidden.mem_ambientHidden.mp hu).1 i hi it
    have mass : row b u=b t*u t := by
      rw [row_apply,dotProduct]
      apply Finset.sum_eq_single t
      · intro i _ hi
        rw [off i hi,mul_zero]
      · simp
    have zt : u t=0 :=
      (mul_eq_zero.mp (mass.symm.trans (Hidden.mem_ambientHidden.mp hu).2)).resolve_left bt
    ext i
    by_cases e : i=t
    · simpa [e] using zt
    · simpa using off i e
  have outside : ∃ j∈G,compensated b t j∉U := by
    by_contra! h
    have Hle : H≤U := by
      intro u hu
      let v : Fin 24→K := ∑ j∈G,u j • compensated b t j
      have vU : v∈U := U.sum_mem (fun j hj=>U.smul_mem _ (h j hj))
      have eq : u-v=0 := by
        apply zero_of_restrict (H.sub_mem hu (hU vU))
        intro i hi
        have it : i≠t := fun e=>ht (e ▸ hi)
        have vi : v i=u i := by
          change (∑ j∈G,u j • compensated b t j) i=u i
          simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,compensated_apply,
            if_neg it,mul_zero,sub_zero]
          rw [Finset.sum_eq_single_of_mem i hi]
          · simp
          · intro j _ ji
            simp [ji.symm]
        change u i-v i=0
        rw [vi,sub_self]
      rw [sub_eq_zero.mp eq]
      exact vU
    have rr := Submodule.finrank_mono Hle
    change finrank K H=4 at rH
    omega
  obtain ⟨j,hj,nj⟩ := outside
  let B := U ⊔ K ∙ compensated b t j
  have inB : compensated b t j∈B :=
    Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have ub : U<B :=
    lt_of_le_of_ne le_sup_left (fun e=>nj (e.symm ▸ inB))
  have rb := Submodule.finrank_lt_finrank_of_lt ub
  have BLe : B≤H := sup_le hU
    ((Submodule.span_singleton_le_iff_mem (compensated b t j) H).mpr (inCarrier j hj))
  have E : B=H := Submodule.eq_of_le_of_finrank_le BLe (by
    change finrank K H≤finrank K B
    change finrank K H=4 at rH
    omega)
  exact ⟨j,hj,E.symm⟩

private theorem compensated_root {c d : Fin 24→K} {o t j : Fin 24}
    (ct : c t=1) (jG : j∈Hidden.blindRows c b d o t)
    (R : K[X]) (rk : R.eval (c j)=0) (i : Fin 24) :
    compensated b t j i*R.eval (c i)=0 := by
  classical
  by_cases ij : i=j
  · rw [ij,rk,mul_zero]
  by_cases it : i=t
  · rw [it]
    by_cases bj : b j=0
    · simp [compensated_apply,bj,show t≠j from fun h=>ij (it.trans h)]
    · have cj : c j=1 :=
        (sub_eq_zero.mp ((mul_eq_zero.mp ((Hidden.mem_blindRows j).mp jG).2.2.2).resolve_right bj)).symm
      rw [←ct] at cj
      rw [←cj,rk,mul_zero]
  · simp [compensated_apply,ij,it]

/-- Exact width census in rank four. The physical seed census need not be
strengthened to simple seed clocks: it is the contrast clocks that become
simple, and the actual origin is in the seed-or-contrast union. -/
private theorem rank_four_contrast_census (L : Width24OrdinaryWeakHead A b U w Q P)
    (ha : ∀ i j,i≤j→A i j=0) (ho : HasOrder 16 A b)
    (rankFour : finrank K (width24WeakFiveCarrier A b)=4)
    (four : (weightedSites (reflectedClock A) (reverseContrast A b Q P)).card=4) :
    let c := nodes A
    let d := quadraticSeed A b
    let t := Fin.last 23
    let V := weakFiveRows A b Q P
    let G := Hidden.blindRows c b d 0 t
    let D := Hidden.activeRows d
    V.card=4 ∧ Set.InjOn (reflectedClock A) (V : Set (Fin 24)) ∧
      (∀ i : Fin 24,i=t ∨ i∈G ∨ i∈D ∨ i∈V) := by
  classical
  dsimp only
  let c := nodes A
  let d := quadraticSeed A b
  let t := Fin.last 23
  let V := weakFiveRows A b Q P
  let G := Hidden.blindRows c b d 0 t
  let D := Hidden.activeRows d
  let C := insert t ((G∪D)∪V)
  let F := width24_paid_frame ha ho
  let cover := width24_quadratic_cover ha ho
  have dt : d t=0 := cover.lastSeed
  have yt : reflectedClock A t=0 := by
    change 1-nodes A (Fin.last 23)=0
    rw [F.lastClock,sub_self]
  have data (i : Fin 24) (hi : i∈V) :
      d i=0 ∧ reflectedClock A i≠0 ∧ b i≠0 ∧ Q.eval (reflectedClock A i)≠0 ∧ w i=0 :=
    reverse_contrast_true_support L.qFit L.pFit i ((mem_weakFiveRows i).mp hi)
  have GD : Disjoint G D := Finset.disjoint_left.mpr fun i hg hd=>
    ((Hidden.mem_activeRows i).mp hd) ((Hidden.mem_blindRows i).mp hg).2.2.1
  have GV : Disjoint G V := Finset.disjoint_left.mpr fun i hg hv=>
    (mul_ne_zero (data i hv).2.1 (data i hv).2.2.1) ((Hidden.mem_blindRows i).mp hg).2.2.2
  have DV : Disjoint D V := Finset.disjoint_left.mpr fun i hd hv=>
    ((Hidden.mem_activeRows i).mp hd) (data i hv).1
  have GW : Disjoint (G∪D) V := Finset.disjoint_union_left.mpr ⟨GV,DV⟩
  have ntV : t∉V := fun h=>(data t h).2.1 yt
  have ntG : t∉G := fun h=>((Hidden.mem_blindRows t).mp h).2.1 rfl
  have ntD : t∉D := fun h=>((Hidden.mem_activeRows t).mp h) dt
  have nt : t∉(G∪D)∪V := by simp [ntV,ntG,ntD]
  have gc : G.card=4 := (Hidden.carrier_rank F.lastLive.live).symm.trans rankFour
  have dc : 15≤D.card := width24_seed_rows_ge_fifteen ha ho
  have img : V.image (reflectedClock A)=weightedSites (reflectedClock A) (reverseContrast A b Q P) := by
    ext r
    simp only [Finset.mem_image,mem_weightedSites,V,mem_weakFiveRows]
  have vl : 4≤V.card := by
    have k := Finset.card_image_le (f:=reflectedClock A) (s:=V)
    rw [img,four] at k
    exact k
  have cc : C.card=G.card+D.card+V.card+1 := by
    change (insert t ((G∪D)∪V)).card=_
    rw [Finset.card_insert_of_notMem nt,Finset.card_union_of_disjoint GW,
      Finset.card_union_of_disjoint GD]
  have upper := Finset.card_le_univ C
  rw [Fintype.card_fin] at upper
  have vc : V.card=4 := by omega
  have all : C=Finset.univ := Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by
    rw [Finset.card_univ,Fintype.card_fin]
    omega)
  change V.card=4 ∧ Set.InjOn (reflectedClock A) (V : Set (Fin 24)) ∧ _
  refine ⟨vc,Finset.card_image_iff.mp (by rw [img,four,vc]),?_⟩
  intro i
  have e : i∈C := by rw [all];exact Finset.mem_univ _
  change i∈insert t ((G∪D)∪V) at e
  simpa only [Finset.mem_insert,Finset.mem_union,or_assoc] using e

/-- Complete true rank-four exclusion at four numerical contrast clocks.
The sixth row is a genuine compensated blind direction. When its numerical
clock is new, the blind condition and absence of reflected zero force its
original b to vanish; no such assertion is used at a repeated clock. -/
theorem Width24OrdinaryWeakHead.weak_four_carrier_four_impossible
    (L : Width24OrdinaryWeakHead A b U w Q P)
    (ha : ∀ i j,i≤j→A i j=0) (ho : HasOrder 16 A b)
    (seven : finrank K (zeroSpace A 7)=7)
    (rankFour : finrank K (width24WeakFiveCarrier A b)=4)
    (four : (weightedSites (reflectedClock A) (reverseContrast A b Q P)).card=4) : False := by
  classical
  let c := nodes A
  let y := reflectedClock A
  let d := quadraticSeed A b
  let t := Fin.last 23
  let V := weakFiveRows A b Q P
  let G := Hidden.blindRows c b d 0 t
  let H := width24WeakFiveCarrier A b
  let D := Hidden.activeRows d
  let F := width24_paid_frame ha ho
  let cover := width24_quadratic_cover ha ho
  have ct : c t=1 := F.lastClock
  have bt : b t≠0 := F.lastLive.live
  have dt : d t=0 := cover.lastSeed
  have yt : y t=0 := by change 1-c t=0;rw [ct,sub_self]
  have c0 : c 0=0 := by
    change (∑ j,A 0 j*(1:K))=0
    exact Finset.sum_eq_zero fun j _=>by rw [ha 0 j (Fin.zero_le j),zero_mul]
  have y0 : y 0=1 := by change 1-c 0=1;rw [c0,sub_zero]
  have n0t : (0:Fin 24)≠t := fun e=>zero_ne_one (c0.symm.trans ((congrArg c e).trans ct))
  have data (i : Fin 24) (hi : i∈V) :
      d i=0 ∧ y i≠0 ∧ b i≠0 ∧ Q.eval (y i)≠0 ∧ w i=0 :=
    reverse_contrast_true_support L.qFit L.pFit i ((mem_weakFiveRows i).mp hi)
  have nt : t∉V := fun h=>(data t h).2.1 yt
  obtain ⟨v4,yi,census⟩ := rank_four_contrast_census L ha ho rankFour four
  have ci : Set.InjOn c (V : Set (Fin 24)) := by
    intro i hi j hj eq
    apply yi hi hj
    change 1-c i=1-c j
    rw [eq]
  obtain ⟨u3,U4,w4,offEight⟩ := L.rank_four_refund ha ho seven rankFour
  obtain ⟨e,eG,split⟩ := compensated_escape bt L.coreInside u3 rankFour
  let κ := c e
  let h := compensated b t e
  change e∈G at eG
  change H=U ⊔ K ∙ h at split
  let q := Q.comp (1-X)
  have qd : q.natDegree≤4 := weak_four_reflected_degree Q L.qDegree
  have refl (x : K) : q.eval x=Q.eval (1-x) := by simp [q,eval_comp]
  have onSeed (i : Fin 24) (hd : i∈D) : w i=q.eval (c i) := by
    have eq := L.qFit i
    change d i*w i=Q.eval (y i)*d i at eq
    rw [mul_comm (Q.eval (y i)) (d i)] at eq
    exact (mul_left_cancel₀ ((Hidden.mem_activeRows i).mp hd) eq).trans (refl (c i)).symm
  obtain ⟨g,hg,fill⟩ := Hidden.carrier_filler (o:=(0:Fin 24))
    (c:=c) (d:=d) (f:=evalNodes A q-w) bt
  change g∈H at hg
  let θ := evalNodes A q-(w+g)
  have mask (i : Fin 24) (it : i≠t) (iv : i∉V) : θ i=0 := by
    rcases census i with eq|ig|hd|vi
    · exact False.elim (it eq)
    · have fi : g i=q.eval (c i)-w i := fill i ig
      change q.eval (c i)-(w i+g i)=0
      rw [fi]
      ring
    · have gi := Hidden.carrier_zero_on_active dt hg ((Hidden.mem_activeRows i).mp hd)
      change q.eval (c i)-(w i+g i)=0
      rw [gi,onSeed i hd,add_zero,sub_self]
    · exact False.elim (iv vi)
  have active (i : Fin 24) (vi : i∈V) : q.eval (c i)≠0 := by
    rw [refl]
    exact (data i vi).2.2.2.1
  rw [split] at hg
  obtain ⟨u,hu,v,hv,gsum⟩ := Submodule.mem_sup.mp hg
  obtain ⟨δ,drep⟩ := Submodule.mem_span_singleton.mp hv
  have gu : g=u+δ • h := by rw [←gsum,←drep]
  have u4 : u∈zeroSpace A 4 := U4 hu
  have z4 : w+u∈zeroSpace A 4 := (zeroSpace A 4).add_mem w4 u4
  have paid (R : K[X]) (rd : R.natDegree≤3) (rk : R.eval κ=0)
      (i : Fin 24) (vi : i∈V) :
      mat A (weightedEval c θ R) i=(primitive (R*q)).eval (c i) := by
    have feed : weightedEval c θ R = evalNodes A (R*q)-(w+u)*evalNodes A R := by
      ext k
      have b0 : h k*R.eval (c k)=0 := compensated_root ct eG R rk k
      simp only [θ,gu,weightedEval_apply,evalNodes_apply,Pi.sub_apply,Pi.add_apply,Pi.smul_apply,
        smul_eq_mul,Pi.mul_apply,eval_mul]
      linear_combination -δ*b0
    have work : (w+u)*evalNodes A R∈zeroSpace A 7 :=
      zeroSpace_mul_treeSpace ho (by decide : 3+1≤16) z4 (evalNodes_mem_treeSpace A R rd)
    have zw := offEight _ (mat_zeroSpace_charZero A 7 work) i vi
    have pp := offEight _ (primitive_defect A (R*q) (natDegree_mul_le_of_le rd qd)) i vi
    change mat A (evalNodes A (R*q)) i-(primitive (R*q)).eval (c i)=0 at pp
    rw [feed,map_sub,Pi.sub_apply,zw,sub_zero,sub_eq_zero.mp pp]
  have pref (R : K[X]) (rd : R.natDegree≤3) (rk : R.eval κ=0)
      (i : Fin 24) (vi : i∈V)
      (pre : ∀ j < i, j ∈ V → R.eval (c j) = 0) :
      (primitive (R*q)).eval (c i)=0 := by
    rw [←paid R rd rk i vi]
    apply causal_mat ha
    intro j ji
    by_cases jv : j∈V
    · simp only [weightedEval_apply,pre j ji jv,zero_mul]
    · have jt : j≠t := by
        intro eq
        rw [eq] at ji
        exact (not_lt_of_ge (Fin.le_last i)) ji
      rw [weightedEval_apply,mask j jt jv,mul_zero]
  have originLive : Q.eval 1≠0 := by
    intro q1
    have q0 : q.eval 0=0 := by rw [refl,sub_zero,q1]
    let T := V.filter (fun i=>c i≠κ)
    let B := V.filter (fun i=>c i=κ)
    have bc : B.card≤1 := Finset.card_le_one.mpr (by
      intro i hi j hj
      obtain ⟨vi,ai⟩ := Finset.mem_filter.mp hi
      obtain ⟨vj,aj⟩ := Finset.mem_filter.mp hj
      exact ci vi vj (ai.trans aj.symm))
    have ucard : B.card+T.card=4 := (Finset.card_filter_add_card_filter_not (s := V) (fun i => c i = κ)).trans v4
    have ts : T.Nonempty := Finset.card_pos.mp (by omega)
    let i := T.min' ts
    have ti : i∈T := T.min'_mem ts
    have vi : i∈V := (Finset.mem_filter.mp ti).1
    let N := T.erase i
    have nc : N.card=T.card-1 := Finset.card_erase_of_mem ti
    have ns : N.Nonempty := Finset.card_pos.mp (by omega)
    let j := N.min' ns
    have nj : j∈N := N.min'_mem ns
    have tj : j∈T := (Finset.mem_erase.mp nj).2
    have vj : j∈V := (Finset.mem_filter.mp tj).1
    have sep : c j≠c i := fun eq=>(Finset.mem_erase.mp nj).1 (ci vj vi eq)
    have live (k : Fin 24) (vk : k∈V) : c k≠0 :=
      fun e=>active k vk (by rw [e,q0])
    let q' := (X-C κ)*q
    have qn : q≠0 := fun eq=>active i vi (by rw [eq,eval_zero])
    have q'n : q'≠0 := mul_ne_zero (X_sub_C_ne_zero _) qn
    have q'0 : q'.eval 0=0 := by simp [q',q0]
    have q'd : q'.natDegree≤5 :=
      natDegree_mul_le_of_le (by rw [natDegree_X_sub_C]) qd
    have dvd : (X:K[X])∣q' := by rw [X_dvd_iff,coeff_zero_eq_eval_zero,q'0]
    obtain ⟨J,rep⟩ := dvd
    have jn : J≠0 := fun eq=>q'n (by rw [rep,eq,mul_zero])
    have jd : J.natDegree≤4 := by rw [rep,natDegree_X_mul jn] at q'd;omega
    apply jn (RKCert.EndpointPhysical.ordered_quartic_eq_zero_of_primitives jd
      (live i vi) (live j vj) sep ⟨?_,?_⟩)
    · intro R rd
      let E := R*(X-C κ)
      have ed : E.natDegree≤3 :=
        natDegree_mul_le_of_le rd (show (X - C κ).natDegree ≤ 1 from (natDegree_X_sub_C κ).le)
      have ek : E.eval κ=0 := by simp [E]
      have p := pref E ed ek i vi (by
        intro k ki kv
        by_cases outside : c k=κ
        · simp [E,outside]
        · exact False.elim ((not_le_of_gt ki) (T.min'_le k (Finset.mem_filter.mpr ⟨kv,outside⟩))))
      rw [formalPrimitive_eq_native,←rep]
      have e : R*q'=E*q := by dsimp only [q',E];ring
      rw [e]
      exact p
    · intro R rd
      let E := (R*(X-C (c i)))*(X-C κ)
      have ed : E.natDegree≤3 := natDegree_mul_le_of_le
        (natDegree_mul_le_of_le rd (show (X-C (c i)).natDegree≤1 by rw [natDegree_X_sub_C]))
        (show (X-C κ).natDegree≤1 by rw [natDegree_X_sub_C])
      have ek : E.eval κ=0 := by simp [E]
      have p := pref E ed ek j vj (by
        intro k kj kv
        by_cases out : c k=κ
        · simp [E,out]
        by_cases same : c k=c i
        · simp [E,same]
        have kn : k∈N :=
          Finset.mem_erase.mpr ⟨fun eq=>same (congrArg c eq),Finset.mem_filter.mpr ⟨kv,out⟩⟩
        exact False.elim ((not_le_of_gt kj) (N.min'_le k kn)))
      rw [formalPrimitive_eq_native]
      have e : R*(X*(X-C (c i))*J)=E*q := calc
        _ = (R*(X-C (c i)))*((X:K[X])*J) := by ring
        _ = _ := by rw [←rep];dsimp only [q',E];ring
      rwa [e]
  have origin : (0:Fin 24)∈V := by
    rcases census 0 with neq|g0|seed|vis
    · exact False.elim (n0t neq)
    · exact False.elim (((Hidden.mem_blindRows 0).mp g0).1 rfl)
    · have prec := onSeed 0 seed
      have wz := origin_zeroSpace ha 4 w4
      change w 0 = 0 at wz
      rw [wz,c0,refl,sub_zero] at prec
      exact False.elim (originLive prec.symm)
    · exact vis
  let C := insert t V
  have eN : e∉C := by
    intro ec
    rcases Finset.mem_insert.mp ec with et|ev
    · exact ((Hidden.mem_blindRows e).mp eG).2.1 et
    · exact (mul_ne_zero (data e ev).2.1 (data e ev).2.2.1)
        ((Hidden.mem_blindRows e).mp eG).2.2.2
  have simple : Set.InjOn y (C : Set (Fin 24)) := by
    intro i hi j hj eq
    rcases Finset.mem_insert.mp hi with hi|hi <;>
      rcases Finset.mem_insert.mp hj with hj|hj
    · exact hi.trans hj.symm
    · rw [hi,yt] at eq
      exact False.elim ((data j hj).2.1 eq.symm)
    · rw [hj,yt] at eq
      exact False.elim ((data i hi).2.1 eq)
    · exact yi hi hj eq
  let θ' := evalNodes A q-(w+u)
  have θchange : θ'=θ+δ • h := by
    rw [show θ=evalNodes A q-(w+g) from rfl,gu]
    change evalNodes A q-(w+u)=evalNodes A q-(w+(u+δ • h))+δ • h
    abel
  have actual : WeakFourGradedMask A b θ' q Q (insert e C) := by
    refine ⟨qd,refl,⟨w+u,z4,rfl⟩,?_,?_⟩
    · intro i off
      have it : i≠t := fun eq=>off (eq.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
      have iv : i∉V := fun h=>off (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
      have ie : i≠e := fun eq=>off (eq.symm ▸ Finset.mem_insert_self _ _)
      have h0 : h i=0 := by simp [h,compensated_apply,ie,it]
      rw [θchange,Pi.add_apply,Pi.smul_apply,mask i it iv,h0,smul_zero,zero_add]
    · intro i hi
      rcases Finset.mem_insert.mp hi with he|hc
      · rw [he]
        exact ((Hidden.mem_blindRows e).mp eG).2.2.1
      · rcases Finset.mem_insert.mp hc with ht|hv
        · rw [ht]
          exact dt
        · exact (data i hv).1
  have cc : C.card=5 := by change (insert t V).card=5;rw [Finset.card_insert_of_notMem nt,v4]
  have extra : (∃ i∈C,y i=y e) ∨ b e=0 := by
    by_cases er : y e=0
    · exact Or.inl ⟨t,Finset.mem_insert_self _ _,yt.trans er.symm⟩
    · exact Or.inr ((mul_eq_zero.mp ((Hidden.mem_blindRows e).mp eG).2.2.2).resolve_left er)
  exact actual.five_plus_one_impossible ha ho L.qNonzero L.qDegree cc eN simple
    ⟨t,Finset.mem_insert_self _ _,yt⟩ ⟨0,Finset.mem_insert_of_mem origin,y0⟩ extra

end
end RKResearch.Certified.ERK16
