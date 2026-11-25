module

public import RKCert.ReviewedNative.ERK13NativeMarkedLobattoSquare
public import RKCert.ReviewedNative.ERK13NativeLateClassChart
public import RKCert.ReviewedNative.NativeQuadraticPairBound
import Mathlib.Data.Finset.Sum
import Mathlib.Tactic.Abel
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Exact mark-separated classes of a high degree-six square

The counted eliminant pays the upper rank bound before clock stability
or algebra closure is assumed. The full original grade ten then fills
the class algebra by the measured lower rank. The literal last row has
its own label, whether or not a previous pair equals its numerical pair. -/

namespace RKResearch.Certified.Graded.ERK13NativeFirst

open RKResearch Polynomial Module Reverse PhysicalCensus ERK13OrdinarySquare
open ERK13NativeLatePhysicalFold (label_orbit_one_iff dead_pair_label_iff)
open RKCert.OneEscape RKCert.Endpoint NativeQuadraticClassSelector
open scoped Classical Matrix BigOperators
noncomputable section

variable {K : Type*} [Field K] [CharZero K]
variable {A : Matrix (Fin 19) (Fin 19) K} {b : Fin 19→K}
variable {U : Submodule K (Fin 19→K)} {w v : Fin 19→K}
variable {G P R Q : K[X]}
set_option maxHeartbeats 1800000
set_option maxRecDepth 2300

/-- No original row other than the actual endpoint is labeled none. -/
def lobattoClass (A : Matrix (Fin 19) (Fin 19) K)
    (U : Submodule K (Fin 19→K)) (v : Fin 19→K) (i : Fin 19) :
    Option ((U→K)⊕(K×K)) :=
  if i=Fin.last 18 then none else some (phaseLabel A U v i)

def lobattoRegularPairs (A : Matrix (Fin 19) (Fin 19) K)
    (U : Submodule K (Fin 19→K)) (v : Fin 19→K) : Finset (K×K) :=
  (Finset.univ.filter (fun i=>i≠Fin.last 18 ∧ ¬LiveCore.live U i)).image (headPair A v)

theorem mem_lobattoRegularPairs {p : K×K} :
    p∈lobattoRegularPairs A U v ↔
      ∃ i : Fin 19, i≠Fin.last 18 ∧ ¬LiveCore.live U i ∧ headPair A v i=p := by
  simp only [lobattoRegularPairs,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and,
    and_assoc]

theorem lobatto_class_not_last_iff {i j : Fin 19} (iL : i≠Fin.last 18) :
    lobattoClass A U v i=lobattoClass A U v j ↔
       j≠Fin.last 18 ∧ phaseLabel A U v i=phaseLabel A U v j := by
  unfold lobattoClass
  rw [ite_eq_right iL]
  by_cases jL : j=Fin.last 18
  · rw [ite_eq_left jL]
    constructor
    · intro h
      cases h
    · intro h
      exact (h.1 jL).elim
  · rw [ite_eq_right jL]
    exact ⟨fun h=>⟨jL,Option.some.inj h⟩,fun h=>congrArg some h.2⟩

theorem lobatto_class_regular_iff {i j : Fin 19} (iL : i≠Fin.last 18)
    (jL : j≠Fin.last 18) (di : ¬LiveCore.live U i) (dj : ¬LiveCore.live U j) :
    lobattoClass A U v i=lobattoClass A U v j ↔ headPair A v i=headPair A v j := by
  rw [lobatto_class_not_last_iff iL, (dead_pair_label_iff di dj),and_iff_right jL]

theorem LobattoSquareSection.eliminant_degree (L : LobattoSquareSection A b U w v G P R Q)
    (top : (G-R*Q).coeff 8≠0) : (eliminant G Q R P).natDegree=14 := by
  have d₈ : (G-R*Q).natDegree=8 := le_antisymm L.delta_cap (le_natDegree_of_ne_zero top)
  have d₆ : G.natDegree=6 := L.head.original.first.degree
  have gn : G≠0 := by intro z; rw [z,natDegree_zero] at d₆; omega
  have dn : G-R*Q≠0 := fun z=>top (by rw [z,coeff_zero])
  have first : ((G-R*Q)*G).natDegree=14 := by rw [natDegree_mul dn gn,d₈,d₆]
  have q2 : (Q^2).natDegree≤2*Q.natDegree := natDegree_pow_le
  have qcap : (Q^2).natDegree≤6 := q2.trans (by have := L.qd; omega)
  have tail : (P*Q^2).natDegree≤11 := natDegree_mul_le_of_le L.pd qcap
  rw [eliminant,natDegree_sub_eq_left_of_natDegree_lt (show (P*Q^2).natDegree<
    ((G-R*Q)*G).natDegree by omega),first]

theorem LobattoSquareSection.regular_laws (L : LobattoSquareSection A b U w v G P R Q) :
    (∀ p∈lobattoRegularPairs A U v,G.eval p.1=Q.eval p.1*p.2) ∧
    (∀ p∈lobattoRegularPairs A U v,p.2^2=R.eval p.1*p.2+P.eval p.1) := by
  obtain ⟨u,hu,sq⟩ := L.square
  obtain ⟨a,ha,me⟩ := L.mesh
  constructor
  · intro p hp
    obtain ⟨i,iL,dead,rfl⟩ := mem_lobattoRegularPairs.mp hp
    simpa only [headPair,evalNodes_apply,weightedEval_apply,Pi.smul_apply,smul_eq_mul,
      Pi.add_apply,coordinate_last_apply_zero iL,LiveCore.val_eq_zero_of_not_live dead ha,
      zero_add,mul_zero,add_zero] using congrFun me i
  · intro p hp
    obtain ⟨i,iL,dead,rfl⟩ := mem_lobattoRegularPairs.mp hp
    simpa only [headPair,pow_two,Pi.mul_apply,evalNodes_apply,weightedEval_apply,Pi.smul_apply,
      smul_eq_mul,Pi.add_apply,Pi.sub_apply,coordinate_last_apply_zero iL,
      LiveCore.val_eq_zero_of_not_live dead hu,mul_zero,add_zero,zero_add,sub_zero,add_comm] using
      congrFun sq i

private theorem last_dead (S : LobattoCleanHead A b 2 U w v G)
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b) :
    ¬LiveCore.live U (Fin.last 18) := by
  rintro ⟨u,hu,nu⟩
  exact nu (early_terminal_zeroSpace_five_last ho S.original.head.paidRanks.lastActive
    (S.original.degree_six_terminal_mem ha ho) (S.original.head.head.coreInside hu))

/-- The mark-separated chart reads clocks, the clean head and all core
columns on classes, without moving the literal terminal. -/
theorem LobattoCleanHead.class_reads (S : LobattoCleanHead A b 2 U w v G)
    {i j : Fin 19} (eq : lobattoClass A U v i=lobattoClass A U v j) :
    nodes A i=nodes A j ∧ v i=v j ∧
      (∀ t∈U,t i=t j) ∧ coordinate (K:=K) (Fin.last 18) i=coordinate (Fin.last 18) j := by
  by_cases iL : i=Fin.last 18
  · have jL : j=Fin.last 18 := by
      by_contra notJ
      exact ((lobatto_class_not_last_iff (A:=A) (U:=U) (v:=v) notJ).mp eq.symm).1 iL
    have ij : i=j := iL.trans jL.symm
    exact ⟨congrArg (nodes A) ij,congrArg v ij,fun t _=>congrArg t ij,
      congrArg (coordinate (K:=K) (Fin.last 18)) ij⟩
  obtain ⟨jL,phase⟩ := (lobatto_class_not_last_iff iL).mp eq
  have sameAxis : coordinate (K:=K) (Fin.last 18) i=coordinate (Fin.last 18) j :=
    (coordinate_last_apply_zero iL).trans (coordinate_last_apply_zero jL).symm
  by_cases li : LiveCore.live U i <;> by_cases lj : LiveCore.live U j
  · have read : coreTrace U i=coreTrace U j :=
      Sum.inl.inj (by simpa only [phaseLabel,if_pos li,if_pos lj] using phase)
    obtain ⟨e,he,mask⟩ := LiveCore.exists_live_indicator U S.coreClosed
    have ce : diag (nodes A) e∈U := S.original.head.head.coreStable (Submodule.mem_map_of_mem he)
    have c := congrFun read (⟨diag (nodes A) e,ce⟩ : U)
    change (diag (nodes A) e) i=(diag (nodes A) e) j at c
    have c' : nodes A i=nodes A j := by
      simpa only [diag_apply,mask i,mask j,if_pos li,if_pos lj,mul_one] using c
    exact ⟨c',(S.clean i li).trans (S.clean j lj).symm,fun t ht=>congrFun read ⟨t,ht⟩,
      sameAxis⟩
  · simp [phaseLabel,li,lj] at phase
  · simp [phaseLabel,li,lj] at phase
  · have pair := (dead_pair_label_iff li lj).mp phase
    exact ⟨congrArg Prod.fst pair,congrArg Prod.snd pair,fun t ht=>
      (LiveCore.val_eq_zero_of_not_live li ht).trans (LiveCore.val_eq_zero_of_not_live lj ht).symm,
      sameAxis⟩

theorem LobattoCleanHead.chart_repr (S : LobattoCleanHead A b 2 U w v G)
    {m : ℕ} (pay : 6+m≤10)
    {z : Fin 19→K} (hz : z∈treeSpace A (6+m)) :
    ∃ (H J : K[X]) (u : Fin 19→K) (a : K), H.natDegree≤5 ∧ J.natDegree<4+m ∧ u∈U ∧
      z=evalNodes A H+weightedEval (nodes A) v J+u+a • coordinate (Fin.last 18) := by
  have hZ : z∈markedTreeSpace A b (6+m) := Submodule.mem_sup_left hz
  have chart := S.chart m pay
  rw [chart] at hZ
  obtain ⟨f,hf,d,hd,e⟩ := Submodule.mem_sup.mp hZ
  obtain ⟨H,Hd,hH⟩ := exists_polynomial_of_coeff_range hf
  obtain ⟨h,hh,r,hr,rForm⟩ := Submodule.mem_sup.mp hd
  rw [terminalMark,if_pos S.original.seed] at hr
  obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hr
  obtain ⟨u,hu,J,Jd,rep⟩ := band_polynomial_repr (by omega : 0<4+m) hh
  refine ⟨H,J,u,a,Hd,Jd,hu,?_⟩
  rw [←e,←hH,←rForm,rep]; abel

private theorem active_core_census (S : LobattoCleanHead A b 2 U w v G)
    {e : Fin 19→K} (he : e∈U) (mask : ∀ i,e i=if LiveCore.live U i then 1 else 0) :
    (coreLabels U).card=3 ∧
    ∀ i,LiveCore.live U i →
      labelSlice (coreTrace U) e (coreTrace U i)∈U := by
  have eOn (i : Fin 19) : e i≠0 ↔ LiveCore.live U i := by
    by_cases live : LiveCore.live U i <;> simp [mask i,live]
  have agree (u : Fin 19→K) (hu : u∈U) (i j : Fin 19) (_ : e i≠0) (_ : e j≠0)
      (eq : coreTrace U i=coreTrace U j) : u i=u j := congrFun eq ⟨u,hu⟩
  have sep (i j : Fin 19) (_ : e i≠0) (_ : e j≠0) (ne : coreTrace U i≠coreTrace U j) :
      ∃ u∈U,u i≠u j := by
    obtain ⟨u,h⟩ := Function.ne_iff.mp ne
    exact ⟨u.val,u.property,h⟩
  have orbit := labelOrbit_eq_of_coordinate_separation S.coreClosed he
    (fun i live=>by rw [mask,if_pos ((eOn i).mp live)])
    (fun u hu i z=>LiveCore.val_eq_zero_of_not_live (fun live=>((eOn i).mpr live) z) hu)
    agree sep
  have same : coreLabels U=activeLabels (coreTrace U) e := by
    apply Finset.ext
    intro a
    simp only [mem_coreLabels,mem_activeLabels,eOn]
  have hu := S.original.head.head.baseRank
  rw [S.original.head.five] at hu
  refine ⟨?_,?_⟩
  · rw [same,←labelOrbit_rank,orbit]
    omega
  · intro i hi
    exact labelSlice_mem_of_coordinate_separation S.coreClosed he agree sep i ((eOn i).mpr hi)

theorem LobattoCleanHead.core_selector (S : LobattoCleanHead A b 2 U w v G)
    (ha : ∀i j,i≤j → A i j=0) (ho : HasOrder 13 A b)
    {i : Fin 19} (hi : LiveCore.live U i) :
    labelIndicator (lobattoClass A U v) (lobattoClass A U v i)∈U := by
  obtain ⟨e,he,mask⟩ := LiveCore.exists_live_indicator U S.coreClosed
  have paid := (active_core_census S he mask).2 i hi
  have id : labelIndicator (lobattoClass A U v) (lobattoClass A U v i)=
      labelSlice (coreTrace U) e (coreTrace U i) := by
    funext j
    have iL : i≠Fin.last 18 := fun e=>last_dead S ha ho (e ▸ hi)
    rw [labelIndicator,labelSlice_apply]
    by_cases jL : j=Fin.last 18
    · have dead : ¬LiveCore.live U j := fun h=>last_dead S ha ho (jL ▸ h)
      have diff : lobattoClass A U v j≠lobattoClass A U v i := fun eq=>
        ((lobatto_class_not_last_iff (A:=A) (U:=U) (v:=v) iL).mp eq.symm).1 jL
      simp only [ite_eq_right diff,mask j,ite_eq_right dead,ite_self]
    · have phase := lobatto_class_not_last_iff (A:=A) (U:=U) (v:=v) (j:=i) jL
      by_cases hj : LiveCore.live U j
      · have triff :
            lobattoClass A U v j=lobattoClass A U v i ↔ coreTrace U j=coreTrace U i := by
          rw [phase,and_iff_right iL]
          simp only [phaseLabel,ite_eq_left hj,ite_eq_left hi,Sum.inl.injEq]
        by_cases tr : coreTrace U j=coreTrace U i
        · simp only [ite_eq_left tr,ite_eq_left (triff.mpr tr),mask j,ite_eq_left hj]
        · have diff : lobattoClass A U v j≠lobattoClass A U v i := fun eq=>tr (triff.mp eq)
          simp only [ite_eq_right tr,ite_eq_right diff]
      · have diff : lobattoClass A U v j≠lobattoClass A U v i := by
          intro eq
          have clash := (phase.mp eq).2
          simp [phaseLabel,hj,hi] at clash
        simp only [ite_eq_right diff,mask j,ite_eq_right hj,ite_self]
  exact id.symm ▸ paid

private theorem label_image_split (S : LobattoCleanHead A b 2 U w v G)
    (ha : ∀i j,i≤j → A i j=0) (ho : HasOrder 13 A b) :
    Finset.univ.image (lobattoClass A U v)=
      insert none (((coreLabels U).disjSum (lobattoRegularPairs A U v)).image some) := by
  apply Finset.ext
  intro a
  cases a with
  | none =>
    constructor
    · intro _; exact Finset.mem_insert_self _ _
    · intro _; exact Finset.mem_image.mpr ⟨Fin.last 18,Finset.mem_univ _,by
        unfold lobattoClass
        rw [ite_eq_left rfl]⟩
  | some a =>
    have inImage : some a ∈ Finset.univ.image (lobattoClass A U v) ↔
        ∃ i : Fin 19,i≠Fin.last 18 ∧ phaseLabel A U v i=a := by
      rw [Finset.mem_image]
      constructor
      · rintro ⟨i,_,eq⟩
        by_cases iL : i=Fin.last 18
        · rw [lobattoClass,ite_eq_left iL] at eq
          cases eq
        · exact ⟨i,iL,by simpa only [lobattoClass,if_neg iL,Option.some.injEq] using eq⟩
      · rintro ⟨i,iL,eq⟩
        exact ⟨i,Finset.mem_univ _,by rw [lobattoClass,if_neg iL,eq]⟩
    have other : some a ∈
        insert none (((coreLabels U).disjSum (lobattoRegularPairs A U v)).image some) ↔
        a∈(coreLabels U).disjSum (lobattoRegularPairs A U v) := by
      constructor
      · intro h
        rcases Finset.mem_insert.mp h with no|yes
        · cases no
        · obtain ⟨k,hk,eq⟩ := Finset.mem_image.mp yes
          exact Option.some.inj eq ▸ hk
      · intro h
        exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨a,h,rfl⟩)
    rw [inImage,other]
    cases a with
    | inl t =>
      rw [Finset.inl_mem_disjSum,mem_coreLabels]
      constructor
      · rintro ⟨i,_,eq⟩
        by_cases h : LiveCore.live U i
        · exact ⟨i,h,Sum.inl.inj (by simpa only [phaseLabel,if_pos h] using eq)⟩
        · simp [phaseLabel,h] at eq
      · rintro ⟨i,h,eq⟩
        exact ⟨i,fun li=>last_dead S ha ho (li ▸ h),by rw [phaseLabel,if_pos h,eq]⟩
    | inr t =>
      rw [Finset.inr_mem_disjSum,mem_lobattoRegularPairs]
      constructor
      · rintro ⟨i,iL,eq⟩
        by_cases h : LiveCore.live U i
        · simp [phaseLabel,h] at eq
        · exact ⟨i,iL,h, Sum.inr.inj (by simpa only [phaseLabel,if_neg h] using eq)⟩
      · rintro ⟨i,iL,h,eq⟩
        exact ⟨i,iL,by rw [phaseLabel,if_neg h,eq]⟩

/-- Measured actual E10 equals the complete algebra on eighteen original
labels. A larger class census is impossible by the counted eliminant. -/
theorem LobattoSquareSection.class_geometry (L : LobattoSquareSection A b U w v G P R Q)
    (ha : ∀i j,i≤j → A i j=0) (ho : HasOrder 13 A b)
    (top : (G-R*Q).coeff 8≠0) :
    (Finset.univ.image (lobattoClass A U v)).card=18 ∧
    (lobattoRegularPairs A U v).card=14 ∧
    treeSpace A 10=labelOrbit (lobattoClass A U v) (1:Fin 19→K) := by
  let f := lobattoClass A U v
  let V := labelOrbit f (1:Fin 19→K)
  obtain ⟨e,he,mask⟩ := LiveCore.exists_live_indicator U L.head.coreClosed
  have coreCount := (active_core_census L.head he mask).1
  have pairLaws := L.regular_laws
  have deg := L.eliminant_degree top
  have nz : eliminant G Q R P≠0 := by intro z; rw [z,natDegree_zero] at deg; omega
  have cap := pair_count_le_eliminant_degree _ pairLaws.1 pairLaws.2 nz
  rw [deg] at cap
  let T : Finset ((U→K)⊕(K×K)) := (coreLabels U).disjSum (lobattoRegularPairs A U v)
  have split : Finset.univ.image f=insert none (T.image some) := label_image_split L.head ha ho
  have absent : (none : Option ((U→K)⊕(K×K)))∉T.image some := by
    intro h
    obtain ⟨k,_,bad⟩ := Finset.mem_image.mp h
    cases bad
  have imageCount : (T.image some).card=T.card :=
    Finset.card_image_of_injective T (fun _ _ h=>Option.some.inj h)
  have pairCount : T.card=3+(lobattoRegularPairs A U v).card := by
    dsimp only [T]
    rw [Finset.card_disjSum,coreCount]
  have count : (Finset.univ.image f).card=3+(lobattoRegularPairs A U v).card+1 := by
    rw [split,Finset.card_insert_of_notMem absent,imageCount,pairCount]
  have actual : finrank K (treeSpace A 10)=18 := by
    have rank := (marked_staircase_ranks13 ha ho L.head.original.head L.head.original.seed).1
      10 (by decide) (by decide)
    rwa [L.head.original.degree_six_tree_eq_marked ha ho (by decide : 7≤10)] at rank
  have inV : treeSpace A 10≤V := by
    intro x hx
    apply (label_orbit_one_iff f x).mpr
    intro i j e
    obtain ⟨F,J,u,g,_,_,hu,form⟩ := L.head.chart_repr (m:=4) (by decide) hx
    obtain ⟨c,amp,core,axis⟩ := L.head.class_reads e
    rw [form]
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,evalNodes_apply,weightedEval_apply,c,amp,core u hu,axis]
  have allLabels : activeLabels f (1:Fin 19→K)=Finset.univ.image f := by
    apply Finset.ext
    intro a
    rw [mem_activeLabels,Finset.mem_image]
    constructor
    · rintro ⟨i,_,eq⟩
      exact ⟨i,Finset.mem_univ _,eq⟩
    · rintro ⟨i,_,eq⟩
      exact ⟨i,(one_ne_zero : (1:K)≠0),eq⟩
  have vRank : finrank K V=(Finset.univ.image f).card :=
    (labelOrbit_rank f (1:Fin 19→K)).trans (congrArg Finset.card allLabels)
  have lower := Submodule.finrank_mono inV
  rw [actual,vRank,count] at lower
  have p14 : (lobattoRegularPairs A U v).card=14 := by omega
  have f18 : (Finset.univ.image f).card=18 := by rw [count,p14]
  exact ⟨f18,p14,Submodule.eq_of_le_of_finrank_le inV (by rw [vRank,f18,actual])⟩

theorem LobattoSquareSection.regular_selector_not_nine
    (L : LobattoSquareSection A b U w v G P R Q)
    (ha : ∀i j,i≤j → A i j=0) (ho : HasOrder 13 A b)
    (top : (G-R*Q).coeff 8≠0) (size : (lobattoRegularPairs A U v).card=14)
    {i : Fin 19} (iL : i≠Fin.last 18) (di : ¬LiveCore.live U i) :
    labelIndicator (lobattoClass A U v) (lobattoClass A U v i)∉treeSpace A 9 := by
  intro pay
  obtain ⟨H,J,u,g,hd,jd,hu,form⟩ := L.head.chart_repr (m:=3) (by decide) pay
  have dd : G.natDegree=6 := L.head.original.first.degree
  have hq := natDegree_mul_le_of_le hd L.qd
  have jg := natDegree_mul_le_of_le (show J.natDegree≤6 by omega) dd.le
  have cap := (natDegree_add_le (H*Q) (J*G)).trans (max_le
    (show (H*Q).natDegree≤12 by omega) (show (J*G).natDegree≤12 by omega))
  have small : (H*Q+J*G).natDegree+1<(lobattoRegularPairs A U v).card := by omega
  have sat := (L.eliminant_degree top).trans size.symm
  obtain ⟨mesh,square⟩ := L.regular_laws
  have inside : headPair A v i∈lobattoRegularPairs A U v :=
    mem_lobattoRegularPairs.mpr ⟨i,iL,di,rfl⟩
  have eq (p : K×K) (hp : p∈lobattoRegularPairs A U v) :
      H.eval p.1+J.eval p.1*p.2=(if p=headPair A v i then 1 else 0) := by
    obtain ⟨j,jL,dj,rfl⟩ := mem_lobattoRegularPairs.mp hp
    have iff := lobatto_class_regular_iff (A:=A) (v:=v) jL iL dj di
    have formJ := (congrFun form j).symm
    by_cases same : headPair A v j=headPair A v i
    · have label := iff.mpr same
      rw [ite_eq_left same]
      simpa only [headPair,labelIndicator,ite_eq_left label,evalNodes_apply,weightedEval_apply,
        Pi.add_apply,Pi.smul_apply,smul_eq_mul,coordinate_last_apply_zero jL,
        LiveCore.val_eq_zero_of_not_live dj hu,add_zero,mul_zero] using formJ
    · have label : lobattoClass A U v j≠lobattoClass A U v i := fun h=>same (iff.mp h)
      rw [ite_eq_right same]
      simpa only [headPair,labelIndicator,ite_eq_right label,evalNodes_apply,weightedEval_apply,
        Pi.add_apply,Pi.smul_apply,smul_eq_mul,coordinate_last_apply_zero jL,
        LiveCore.val_eq_zero_of_not_live dj hu,add_zero,mul_zero] using formJ
  have vanish (p : K×K) (hp : p∈lobattoRegularPairs A U v) (np : p≠headPair A v i) :
      H.eval p.1+J.eval p.1*p.2=0 := by simpa only [if_neg np] using eq p hp
  have z := no_singleton_of_saturation mesh square sat small inside vanish
  have here := eq _ inside
  rw [z,if_pos rfl] at here
  exact zero_ne_one here

end
end RKResearch.Certified.Graded.ERK13NativeFirst
