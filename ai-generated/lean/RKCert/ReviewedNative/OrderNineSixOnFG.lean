module
public import RKCert.ReviewedNative.OrderNineSixOnLate
public import RKCert.ReviewedNative.OrderNineSixOnWeights

@[expose] public section

/-! # Physical five-six chart earns the two affine equations, distinct roots and the late scalar port. -/
namespace RKResearch.Certified.Graded.MultiOff
open RKResearch Module Polynomial OneOff Reverse RKCert.Endpoint
open scoped Matrix Classical
variable {K : Type*} [Field K] 

section Ordered
variable [LinearOrder K] [IsStrictOrderedRing K]

structure ActualSixOnFG (A : Matrix (Fin 12) (Fin 12) K) (P : K[X]) where
  first : Fin 10
  middle : Fin 10
  first_lt_middle : first<middle
  middle_lt_late : middle<(8:Fin 10)
  first_clean : g A (lowPrefix10 first)=0
  middle_clean : g A (lowPrefix10 middle)=0
  late_u_clean : g A (lowPrefix10 (8:Fin 10))=0
  late_v_clean : g A (lowPrefix10 (Fin.last 9))=0
  first_nonzero : nodes A (lowPrefix10 first)≠0
  middle_nonzero : nodes A (lowPrefix10 middle)≠0
  late_u_nonzero : nodes A (lowPrefix10 (8:Fin 10))≠0
  late_v_nonzero : nodes A (lowPrefix10 (Fin.last 9))≠0
  first_min : ∀ j : Fin 10,j<first → g A (lowPrefix10 j)=0 → nodes A (lowPrefix10 j)=0
  penultimate_max : ∀ j : Fin 10,middle<j → j≠8 → j≠Fin.last 9 → g A (lowPrefix10 j)≠0
  pencil_parameter : K
  affine_parameter : K
  head_scale : K
  head_scale_nonzero : head_scale≠0
  head_shape : ∀ x, P.eval x=head_scale*(RKCert.Paired.fixedRadauP0 (nodes A (lowPrefix10 first)) x+
    affine_parameter*RKCert.Paired.fixedRadauP1 (nodes A (lowPrefix10 first)) x)
  root_set_injective : Function.Injective (![nodes A (lowPrefix10 first),nodes A (lowPrefix10 middle),
    nodes A (lowPrefix10 (8:Fin 10)),nodes A (lowPrefix10 (Fin.last 9))] : Fin 4→K)
  pencil_roots : ∀ i : Fin 4,(RKCert.Paired.lobattoPencil pencil_parameter).eval
    ((![nodes A (lowPrefix10 first),nodes A (lowPrefix10 middle),
      nodes A (lowPrefix10 (8:Fin 10)),nodes A (lowPrefix10 (Fin.last 9))] : Fin 4→K) i)=0
  D_nonzero : RKCert.Paired.radauLateD (nodes A (lowPrefix10 (8:Fin 10))) (nodes A (lowPrefix10 (Fin.last 9)))≠0
  cubic_v_nonzero : RKCert.Paired.lobattoCubic.eval (nodes A (lowPrefix10 (Fin.last 9)))≠0
  eighth_off_clock : g A (lowPrefix10 (7:Fin 10))≠0 →
    RKCert.Paired.radauLateL (nodes A (lowPrefix10 (8:Fin 10))) (nodes A (lowPrefix10 (Fin.last 9)))
      (nodes A (lowPrefix10 (7:Fin 10)))=0
  F_zero : RKCert.Paired.sixOnF (nodes A (lowPrefix10 (8:Fin 10))) (nodes A (lowPrefix10 (Fin.last 9)))
    (fun x=>RKCert.Paired.fixedRadauP0 (nodes A (lowPrefix10 first)) x+
      affine_parameter*RKCert.Paired.fixedRadauP1 (nodes A (lowPrefix10 first)) x)=0
  G_zero : RKCert.Paired.sixOnG (nodes A (lowPrefix10 middle)) (nodes A (lowPrefix10 (8:Fin 10)))
    (nodes A (lowPrefix10 (Fin.last 9)))
    (fun x=>RKCert.Paired.fixedRadauP0 (nodes A (lowPrefix10 first)) x+
      affine_parameter*RKCert.Paired.fixedRadauP1 (nodes A (lowPrefix10 first)) x)=0

set_option maxHeartbeats 1400000 in
/-- The two scalar constraints in the manuscript arise from the actual
physical tableau. The four roots are in literal chronological on order. -/
theorem order9_actual_five_six_FG
    {A : Matrix (Fin 12) (Fin 12) K} {b : (Fin 12→K)} (ha : ∀i j,i≤j → A i j=0)
    (ho : HasOrder A b 9)
    (hN : (offKnots A).card=5) (hM : (cleanKnots A).card=6)
    {P : K[X]} (hPd : P.natDegree≤2) (hPn : P≠0)
    (hF : zeroSpace A 4=band A 2)
    (hP : ∀ i,g A i≠0 → P.eval (nodes A i)=g A i) :
    Nonempty (ActualSixOnFG A P) := by
  let _ : DecidableEq K := fun _ _ => Classical.propDecidable _
  obtain ⟨d⟩ := order9_five_six_late_rows ha ho hN hM
  obtain ⟨hInject,_,_,_⟩ := order9_five_six_ten_distinct_prefix ha ho hN hM
  change Function.Bijective (fun i : Fin 10 => lowNonterminalStateAt ha (lowPrefix10 i)) at hInject
  obtain ⟨_,_,_,hEndOn,hEndClock,_,hUnique⟩ := order9_five_six_stage_chart ha ho hN hM hP
  have hone : (1:K)∈cleanKnots A := mem_cleanKnots.mpr ⟨Fin.last 11,hEndOn,hEndClock⟩
  let c := nodes A ∘ lowPrefix10
  let B := prefixMat10 A
  let w := gatherRow d.rep (withoutLast12 b)
  let L := lateResidual B c w
  have haB : ∀ i j,i≤j → B i j=0 := prefixMat10_strict ha
  let iU : Fin 10 := 8
  let iV : Fin 10 := Fin.last 9
  let u := c iU
  let v := c iV
  have hL1 (i : Fin 10) : L 1 i=d.nu*d.psi i := congrFun d.eq1 i
  have hL2 (i : Fin 10) : L 2 i=d.alpha*d.psi i := congrFun d.eq2 i
  have hL3 (i : Fin 10) : L 3 i=(d.beta+d.gamma*c i)*d.psi i := congrFun d.eq3 i
  have hV1 : w iV*(1-v)^2=2*d.nu*d.psi iV := by
    have he := hL1 iV
    change -transMat B (fun j => w j*(1-c j^1)) (Fin.last 9) +
      w iV*((1-v)-(1-v^2)/2)=_ at he
    rw [transMat_last_zero haB] at he
    have h : (1-v)-(1-v^2)/2= (1-v)^2/2 := by ring
    rw [neg_zero,zero_add,h] at he
    linear_combination 2*he
  have hV2 : w iV*(v+2)*(1-v)^2=3*d.alpha*d.psi iV := by
    have he := hL2 iV
    change -transMat B (fun j => w j*(1-c j^2)) (Fin.last 9) +
      w iV*((1-v)-(1-v^3)/3)=_ at he
    rw [transMat_last_zero haB] at he
    linear_combination 3*he
  have hOnlyV (j : Fin 10) (hj : iU < j) : j=iV := by
    apply Fin.ext
    change 8 < j.val at hj
    have := j.isLt
    change j.val=9
    omega
  have hU2 : w iU*(1-u)^2*RKCert.Paired.radauLateD u v=6*(d.alpha-(1+v)*d.nu)*d.psi iU := by
    have he := lateResidual_two_combine haB c w iU v (fun j hj => by rw [hOnlyV j hj])
    change 6*(L 2 iU-(1+v)*L 1 iU)=_ at he
    rw [hL1,hL2] at he
    linear_combination -he
  have hA : 3*d.alpha=2*d.nu*(v+2) := by
    apply mul_right_cancel₀ (d.psi_nonzero iV)
    linear_combination (v+2)*hV1-hV2
  have hU : w iU*(1-u)^2*RKCert.Paired.radauLateD u v=2*d.nu*(1-v)*d.psi iU := by
    linear_combination hU2+2*d.psi iU*hA
  have hVnz : 2*d.nu*d.psi iV≠0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) d.nu_nonzero) (d.psi_nonzero iV)
  have hVn : v≠1 := by
    intro hz
    rw [hz,sub_self,zero_pow (by decide : (2:ℕ)≠0),mul_zero] at hV1
    exact hVnz hV1.symm
  have hUvNz : 2*d.nu*(1-v)*d.psi iU≠0 := mul_ne_zero
    (mul_ne_zero (mul_ne_zero (by norm_num) d.nu_nonzero) (sub_ne_zero.mpr (Ne.symm hVn)))
    (d.psi_nonzero iU)
  have hVOn : g A (lowPrefix10 iV)=0 := by
    by_contra h
    have ez := d.off_zero iV h
    change w iV=0 at ez
    rw [ez,zero_mul] at hV1
    exact hVnz hV1.symm
  have hUOn : g A (lowPrefix10 iU)=0 := by
    by_contra h
    have ez := d.off_zero iU h
    change w iU=0 at ez
    rw [ez,zero_mul,zero_mul] at hU
    exact hUvNz hU.symm
  have no1 (i : Fin 10) (hi : g A (lowPrefix10 i)=0) : c i≠1 := by
    intro e
    have z := congrArg Fin.val (hUnique _ hi e)
    change i.val=11 at z
    omega
  have hInjectOn {i j : Fin 10} (hi : g A (lowPrefix10 i)=0)
      (hj : g A (lowPrefix10 j)=0) (h : c i=c j) : i=j :=
    hInject.1 ((lowNonterminalState_eq_iff ha (no1 i) (no1 j)).mpr
      (lowState_eq_iff.mpr ⟨by rw [hi,hj],h⟩))
  have hZeroD : g A (lowPrefix10 0)=0 := origin_zeroSpace ha 2 (mDef_mem A 1)
  have hZeroC : c 0=0 := by
    change (∑ j,A (0:Fin 12) j*1)=0
    exact Finset.sum_eq_zero fun j _=>by rw [ha 0 j (Fin.zero_le _),zero_mul]
  have hU0 : u≠0 := fun h => (by decide : iU≠0) (hInjectOn hUOn hZeroD (h.trans hZeroC.symm))
  have hV0 : v≠0 := fun h => (by decide : iV≠0) (hInjectOn hVOn hZeroD (h.trans hZeroC.symm))
  have huv : u≠v := fun h => (by decide : iU≠iV) (hInjectOn hUOn hVOn h)
  let J := RKCert.Paired.endpointErase (cleanKnots A) 1
  have onWitness (x : K) (hx : x∈J) :
      ∃ i : Fin 10, g A (lowPrefix10 i)=0 ∧ c i=x := by
    obtain ⟨i,hi⟩ := hInject.2 (Sum.inl ⟨x,hx⟩)
    by_cases h : g A (lowPrefix10 i)=0
    · refine ⟨i,h,?_⟩
      have hn : nodes A (lowPrefix10 i)≠1 := no1 i h
      simpa [lowNonterminalStateAt,h,hn,c] using hi
    · simp [lowNonterminalStateAt,h] at hi
  let S := RKCert.Paired.endpointErase J 0
  have hJ0 : (0:K)∈J := Finset.mem_erase.mpr ⟨zero_ne_one,zero_mem_cleanKnots ha⟩
  have hSc : S.card=4 := by
    have h := Finset.card_erase_add_one hJ0
    have hj := Finset.card_erase_add_one hone
    change S.card+1=J.card at h
    change J.card+1=(cleanKnots A).card at hj
    omega
  let H : Set (Fin 10) := {i | g A (lowPrefix10 i)=0 ∧ c i≠0}
  obtain ⟨ih,⟨hhOn,hh0⟩,hMin⟩ := wellFounded_lt.has_min H ⟨iU,hUOn,hU0⟩
  let T : Set (Fin 10) := {i | g A (lowPrefix10 i)=0 ∧ c i≠0 ∧ i≠iU ∧ i≠iV}
  have hT : T.Nonempty := by
    by_contra hh
    have ss : S⊆({u,v}:Finset K) := by
      intro x hx
      obtain ⟨hx0,hxS⟩ := Finset.mem_erase.mp hx
      obtain ⟨k,hk,hxk⟩ := onWitness x hxS
      by_cases hxu : x=u
      · simp [hxu]
      by_cases hxv : x=v
      · simp [hxv]
      exact False.elim (hh ⟨k,hk,fun hz => hx0 (hxk.symm.trans hz),
        fun hz => hxu (hxk.symm.trans (congrArg c hz)),
        fun hz => hxv (hxk.symm.trans (congrArg c hz))⟩)
    have hz := Finset.card_le_card ss
    rw [hSc,Finset.card_pair huv] at hz
    omega
  obtain ⟨ir,⟨hrOn,hr0,hrU,hrV⟩,hMax⟩ := wellFounded_gt.has_min T hT
  let h := c ih
  let r := c ir
  have hrLt : ir < iU := by
    change ir.val < 8
    have hn1 : ir.val≠8 := fun h => hrU (Fin.ext h)
    have hn2 : ir.val≠9 := fun h => hrV (Fin.ext h)
    have := ir.isLt
    omega
  have hhLe : ih ≤ ir := le_of_not_gt (hMin ir ⟨hrOn,hr0⟩)
  have hhr : ih≠ir := by
    intro he
    have ss : S⊆({r,u,v}:Finset K) := by
      intro x hx
      obtain ⟨hx0,hxS⟩ := Finset.mem_erase.mp hx
      obtain ⟨j,hj,hxj⟩ := onWitness x hxS
      by_cases hjU : j=iU
      · have : x=u := hxj.symm.trans (congrArg c hjU)
        simp [this]
      by_cases hjV : j=iV
      · have : x=v := hxj.symm.trans (congrArg c hjV)
        simp [this]
      have hNj : c j≠0 := fun hz => hx0 (hxj.symm.trans hz)
      have hjL : ir ≤ j := he ▸ le_of_not_gt (hMin j ⟨hj,hNj⟩)
      have hjR : j ≤ ir := le_of_not_gt (hMax j ⟨hj,hNj,hjU,hjV⟩)
      have : x=r := hxj.symm.trans (congrArg c (le_antisymm hjR hjL))
      simp [this]
    have hz := Finset.card_le_card ss
    have hz' : ({r,u,v}:Finset K).card≤3 :=
      (Finset.card_insert_le _ _).trans (by rw [Finset.card_pair huv])
    omega
  have hAfter (j : Fin 10) (hj : ir < j) : w j=0 ∨ c j=u ∨ c j=v := by
    by_cases hOn : g A (lowPrefix10 j)=0
    · have hnode : c j≠0 := by
        intro hn
        have j0 := hInjectOn hOn hZeroD (hn.trans hZeroC.symm)
        subst j; exact (not_lt_of_ge (Fin.zero_le ir)) hj
      by_cases hJU : j=iU
      · exact Or.inr (Or.inl (congrArg c hJU))
      by_cases hJV : j=iV
      · exact Or.inr (Or.inr (congrArg c hJV))
      exact False.elim (hMax j ⟨hOn,hnode,hJU,hJV⟩ hj)
    · exact Or.inl (d.off_zero _ hOn)
  have hTriple (i : Fin 10) (ha' : ∀ j, i < j → w j=0 ∨ c j=u ∨ c j=v) :
      12*RKCert.Paired.radauLateE u v d.nu d.alpha d.beta d.gamma (c i)*d.psi i=
        w i*(1-c i)^2*RKCert.Paired.radauLateDn u v (c i) := by
    have he := lateResidual_three_combine haB c w i u v ha'
    change 12*(L 3 i-(1+u+v)*L 2 i+(u+v+u*v)*L 1 i)=_ at he
    rw [hL1,hL2,hL3] at he
    unfold RKCert.Paired.radauLateE
    linear_combination he
  obtain ⟨notD,eU,eR⟩ := RKCert.Paired.fixedRadau_late_column_equations u v r _ _ _ _ _ _
    d.nu d.alpha d.beta d.gamma huv hVn (d.psi_nonzero iU) (d.psi_nonzero iV) d.nu_nonzero
    hV1 hV2 hU2
    (hTriple iU (fun j hj => Or.inr (Or.inr (congrArg c (hOnlyV j hj)))))
    (hTriple iV (fun j hj => False.elim ((not_lt_of_ge (Fin.le_last j)) hj)))
    (hTriple ir hAfter)
  have hPort : g A (lowPrefix10 (7:Fin 10))≠0 → RKCert.Paired.radauLateL u v (c 7)=0 := by
    intro off
    have after (j : Fin 10) (hj : (7:Fin 10)<j) : w j=0 ∨ c j=u ∨ c j=v := by
      change 7<j.val at hj
      have h : j.val=8 ∨ j.val=9 := by have := j.isLt; omega
      rcases h with h|h
      · exact Or.inr (Or.inl (congrArg c (Fin.ext h : j=iU)))
      · exact Or.inr (Or.inr (congrArg c (Fin.ext h : j=iV)))
    obtain ⟨_,_,e⟩ := RKCert.Paired.fixedRadau_late_column_equations u v (c 7) _ _ _ _ _ _
      d.nu d.alpha d.beta d.gamma huv hVn (d.psi_nonzero iU) (d.psi_nonzero iV) d.nu_nonzero
      hV1 hV2 hU2
      (hTriple iU (fun j hj => Or.inr (Or.inr (congrArg c (hOnlyV j hj)))))
      (hTriple iV (fun j hj => False.elim ((not_lt_of_ge (Fin.le_last j)) hj)))
      (hTriple 7 after)
    have ez : w 7=0 := d.off_zero 7 off
    rw [ez,zero_mul,zero_mul,zero_mul] at e
    have n : -2*d.nu*(1-v)*d.psi 7≠0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) d.nu_nonzero)
        (sub_ne_zero.mpr (Ne.symm hVn))) (d.psi_nonzero 7)
    exact (mul_eq_zero.mp (show (-2*d.nu*(1-v)*d.psi 7)*RKCert.Paired.radauLateL u v (c 7)=0 by
      linear_combination -e)).resolve_left n
  have hOff : ∀ x∈offKnots A, offMass A b x=0 :=
    fun x hx => offMass_zero_of_head ho hP (by omega) x hx
  obtain ⟨TZ,hTZ,normB⟩ := order9_six_on_weight_norm (s:=11) ha ho hM hone hOff
  let vRaw := transMat A (orderAdjoint A b 1)
  have hvRaw : vRaw∈annih (treeSpace A 5) := annih_map_transpose (mat_treeSpace A 5) (Submodule.mem_map_of_mem (orderAdjoint_annih ho (k:=1) (j:=6) (by decide)))
  have vEnd : vRaw (Fin.last 11)=0 := transMat_last_zero ha _
  have endW := onWeight_one_of_unique_zero vRaw vEnd hUnique
  obtain ⟨SZ,normW⟩ := five_six_annihilator_weight_norm hvRaw hM hPd hP hone endW
  let q (i : Fin 10) := RKCert.Paired.nodalSlope J (c i)
  have jmem (i : Fin 10) (hi : g A (lowPrefix10 i)=0) : c i∈J :=
    Finset.mem_erase.mpr ⟨no1 i hi,mem_cleanKnots.mpr ⟨_,hi,rfl⟩⟩
  have hQB (i : Fin 10) (hi : g A (lowPrefix10 i)=0) (hc : c i≠0) :
      w i*(1-c i)*q i*RKCert.Paired.lobattoCubic.eval (c i)=TZ := by
    change gatherRow d.rep (withoutLast12 b) i * _ * _ * _ = _
    rw [d.on_b i hi]
    exact normB _ (jmem i hi) hc
  have normPsi (i : Fin 10) (hi : g A (lowPrefix10 i)=0) : d.psi i*P.eval (c i)*q i=SZ := by
    rw [d.on_psi i hi]
    exact normW _ (jmem i hi)
  obtain ⟨hFF,hGG⟩ := RKCert.Paired.sixOn_FG_of_late_weights u v r _ _ _ _ _ _ d.nu
    (q iU) (q iV) (q ir) TZ SZ P.eval hTZ hV1 eU eR
    (hQB iU hUOn hU0) (hQB iV hVOn hV0) (hQB ir hrOn hr0)
    (normPsi iU hUOn) (normPsi iV hVOn) (normPsi ir hrOn)
  have hp0 := (first_nonzero_on_forces_head_shape ha hF hPd hPn hP
    ⟨lowPrefix10 ih,hhOn,hh0⟩).1
  have hJ : (primitive (X*P)).eval h=0 := by
    apply on_primitive_zero_of_prefix ha hF hhOn (X*P)
      (natDegree_mul_le_of_le (by simp) hPd) (diag (nodes A) (g A))
      (clean_mixed_defect hF hhOn)
    intro j hj
    by_cases hdj : g A j=0
    · have hjv : j.val<10 := lt_trans hj ih.isLt
      let k : Fin 10 := ⟨j.val,hjv⟩
      have hkk : lowPrefix10 k=j := Fin.ext rfl
      have hn : nodes A j=0 := by
        by_contra hn
        apply hMin k ⟨by rwa [hkk],by change nodes A (lowPrefix10 k)≠0; rwa [hkk]⟩
        exact hj
      simp [hdj,hn]
    · simp [hP j hdj]
  obtain ⟨a,s,ha0,hs⟩ := first_on_quadratic_shape P hPd h hh0 hp0 hJ
  let W : Fin 4→K := ![h,r,u,v]
  let Q (x : K) := RKCert.Paired.fixedRadauP0 h x+s*RKCert.Paired.fixedRadauP1 h x
  have hFQ : RKCert.Paired.sixOnF u v Q=0 := by
    have hEq : RKCert.Paired.sixOnF u v P.eval=a*RKCert.Paired.sixOnF u v Q := by
      simp only [RKCert.Paired.sixOnF,hs,Q]; ring
    rw [hFF] at hEq
    exact (mul_eq_zero.mp hEq.symm).resolve_left ha0
  have hGQ : RKCert.Paired.sixOnG r u v Q=0 := by
    have hEq : RKCert.Paired.sixOnG r u v P.eval=a*RKCert.Paired.sixOnG r u v Q := by
      simp only [RKCert.Paired.sixOnG,hs,Q]; ring
    rw [hGG] at hEq
    exact (mul_eq_zero.mp hEq.symm).resolve_left ha0
  obtain ⟨param,hRad⟩ := order9_six_on_pencil (s:=11) ha ho hM hone hOff
  have hRoot (i : Fin 10) (hi : g A (lowPrefix10 i)=0) (hc : c i≠0) :
      (RKCert.Paired.lobattoPencil param).eval (c i)=0 := by
    rw [←hRad]
    exact nodalHull_eval_of_mem (Finset.mem_erase.mpr ⟨hc,jmem i hi⟩)
  have rootW : ∀ i, (RKCert.Paired.lobattoPencil param).eval (W i)=0 := by
    intro i
    fin_cases i
    · exact hRoot ih hhOn hh0
    · exact hRoot ir hrOn hr0
    · exact hRoot iU hUOn hU0
    · exact hRoot iV hVOn hV0
  have hhu : ih < iU := lt_of_le_of_lt hhLe hrLt
  have hhv : ih < iV := hhu.trans (by decide)
  have hrv : ir < iV := hrLt.trans (by decide)
  have hnHR : h≠r := fun e => hhr (hInjectOn hhOn hrOn e)
  have hnHU : h≠u := fun e => (ne_of_lt hhu) (hInjectOn hhOn hUOn e)
  have hnHV : h≠v := fun e => (ne_of_lt hhv) (hInjectOn hhOn hVOn e)
  have hnRU : r≠u := fun e => (ne_of_lt hrLt) (hInjectOn hrOn hUOn e)
  have hnRV : r≠v := fun e => (ne_of_lt hrv) (hInjectOn hrOn hVOn e)
  have injW : Function.Injective W := by
    intro i j he
    fin_cases i <;> fin_cases j <;>
      first
      | rfl
      | exact (hnHR he).elim
      | exact (hnHR he.symm).elim
      | exact (hnHU he).elim
      | exact (hnHU he.symm).elim
      | exact (hnHV he).elim
      | exact (hnHV he.symm).elim
      | exact (hnRU he).elim
      | exact (hnRU he.symm).elim
      | exact (hnRV he).elim
      | exact (hnRV he.symm).elim
      | exact (huv he).elim
      | exact (huv he.symm).elim
  have vn : RKCert.Paired.lobattoCubic.eval v≠0 := by
    intro h
    have e := hQB iV hVOn hV0
    rw [show RKCert.Paired.lobattoCubic.eval (c iV)=0 from h,mul_zero] at e
    exact hTZ e.symm
  refine ⟨⟨ih,ir,lt_of_le_of_ne hhLe hhr,hrLt,hhOn,hrOn,hUOn,hVOn,hh0,hr0,hU0,hV0,?_,?_,
    param,s,a,ha0,hs,injW,rootW,notD,vn,hPort,hFQ,hGQ⟩⟩
  · intro i hi g
    by_contra e
    exact hMin i ⟨g,e⟩ hi
  · intro j hj hJU hJV g
    have n : c j≠0 := by
      intro e
      have j0 := hInjectOn g hZeroD (e.trans hZeroC.symm)
      subst j
      exact (not_lt_of_ge (Fin.zero_le ir)) hj
    exact hMax j ⟨g,n,hJU,hJV⟩ hj



end Ordered
end RKResearch.Certified.Graded.MultiOff
