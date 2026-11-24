module
public import RKCert.ReviewedNative.OrderNineCohortRadauLate

@[expose] public section

/-! # Actual five-off/five-clean exclusion and exact six-clean dispatch -/
namespace RKResearch.Certified.Graded.MultiOff
open RKResearch Module Polynomial OneOff Reverse RKCert.Endpoint
open scoped Matrix Classical
variable {K : Type*} [Field K] [CharZero K] {s p : ℕ}

omit [CharZero K] in
theorem transMat_last_zero {A : Matrix (Fin (s+1)) (Fin (s+1)) K}
    (ha : ∀ i j,i≤j → A i j=0) (v : Fin (s+1)→K) : transMat A v (Fin.last s)=0 :=
  Reverse.transpose_tail_zero ha (fun j hj=>False.elim ((not_lt_of_ge (Fin.le_last j)) hj)) le_rfl

omit [CharZero K] in
theorem transMat_zero_of_later_zero {B : Matrix (Fin s) (Fin s) K} (ha : ∀ i j,i≤j → B i j=0)
    (i : Fin s) (w : (Fin s→K)) (h : ∀ j, i < j → w j=0) :
    transMat B w i=0 := by
  simp only [transMat,mat_apply,Matrix.mulVec,dotProduct,Matrix.transpose_apply]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : i < j
  · rw [h j hj,mul_zero]
  · rw [ha j i (le_of_not_gt hj),zero_mul]

theorem lateResidual_two_combine {B : Matrix (Fin s) (Fin s) K} (ha : ∀ i j,i≤j → B i j=0)
    (c b : (Fin s→K)) (i : Fin s) (v : K)
    (h : ∀ j, i < j → c j=v) :
    6*(lateResidual B c b 2 i-(1+v)*lateResidual B c b 1 i) =
      b i*(1-c i)^2*RKCert.Paired.radauLateD (c i) v := by
  let w (k : ℕ) : (Fin s→K) := fun j=>b j*(1-c j^k)
  have hn := transMat_zero_of_later_zero ha i (w 2-(1+v) • w 1) (fun j hj => by
    simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,w,pow_one,h j hj]
    ring)
  rw [map_sub,map_smul,Pi.sub_apply,Pi.smul_apply,smul_eq_mul] at hn
  unfold lateResidual RKCert.Paired.radauLateD
  simp only [Pi.add_apply,Pi.neg_apply,Nat.reduceAdd,Nat.cast_ofNat]
  change _=_
  linear_combination -6*hn

theorem lateResidual_three_combine {B : Matrix (Fin s) (Fin s) K} (ha : ∀ i j,i≤j → B i j=0)
    (c b : (Fin s→K)) (i : Fin s) (u v : K)
    (h : ∀ j, i < j → b j=0 ∨ c j=u ∨ c j=v) :
    12*(lateResidual B c b 3 i-(1+u+v)*lateResidual B c b 2 i+
       (u+v+u*v)*lateResidual B c b 1 i) =
      b i*(1-c i)^2*RKCert.Paired.radauLateDn u v (c i) := by
  let w (k : ℕ) : (Fin s→K) := fun j=>b j*(1-c j^k)
  have hn := transMat_zero_of_later_zero ha i (w 3-(1+u+v) • w 2+(u+v+u*v) • w 1) (fun j hj => by
    simp only [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,w,pow_one]
    rcases h j hj with hg|hu|hv
    · rw [hg]; ring
    · rw [hu]; ring
    · rw [hv]; ring)
  rw [map_add,map_sub,map_smul,map_smul,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,
    Pi.smul_apply,smul_eq_mul,smul_eq_mul] at hn
  unfold lateResidual RKCert.Paired.radauLateDn
  simp only [Pi.add_apply,Pi.neg_apply,Nat.reduceAdd,Nat.cast_ofNat]
  linear_combination -12*hn

theorem first_on_quadratic_shape (P : K[X]) (hP : P.natDegree≤2) (h : K)
    (hne : h≠0) (h0 : P.eval 0≠0) (hJ : (primitive (X*P)).eval h=0) :
    ∃ A B : K, A≠0 ∧
      ∀ x, P.eval x=A*(RKCert.Paired.fixedRadauP0 h x+B*RKCert.Paired.fixedRadauP1 h x) := by
  have d : P.coeff 0≠0 := (coeff_zero_eq_eval_zero P).symm ▸ h0
  let a := P.coeff 0/(3*h^2)
  let b := P.coeff 1*h/P.coeff 0
  have c0 : a*(3*h^2)=P.coeff 0 := div_mul_cancel₀ _ (by
    exact mul_ne_zero (by norm_num) (pow_ne_zero _ hne))
  have c1 : a*b*(3*h)=P.coeff 1 := by
    dsimp [a,b]
    field_simp [d,hne]
  rw [←scalar_primitive (X*P),RKCert.Paired.primitive_eval_X_quadratic P hP] at hJ
  have hJ' : 6*P.coeff 0+4*P.coeff 1*h+3*P.coeff 2*h^2=0 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hne)
    linear_combination 12*hJ
  have c2 : a*(-6-4*b)=P.coeff 2 := by
    dsimp [a,b]
    field_simp [d,hne]
    linear_combination -hJ'
  refine ⟨a,b,div_ne_zero d (mul_ne_zero (by norm_num) (pow_ne_zero _ hne)),?_⟩
  intro x
  conv_lhs => rw [RKCert.Paired.quadratic_coeff_expand P hP]
  simp only [eval_add,eval_monomial,pow_zero,pow_one,mul_one,RKCert.Paired.fixedRadauP0,RKCert.Paired.fixedRadauP1]
  linear_combination -c0 - x*c1 - x^2*c2

set_option maxHeartbeats 550000 in
/-- Both ranks of E5 in the five-on/five-off branch are excluded. -/
theorem order9_no_five_off_five_on
    {A : Matrix (Fin 12) (Fin 12) K} {b : (Fin 12→K)} (ha : ∀i j,i≤j → A i j=0)
    (ho : HasOrder A b 9)
    (hN : (offKnots A).card=5) (hM : (cleanKnots A).card=5) : False := by
  obtain ⟨P,hPd,hPn,_,hF,hP⟩ := order9_two_curve_head ha ho (by decide) (by omega)
  obtain ⟨d⟩ := order9_fixed_radau_late_data ha ho hN hM hPd hF hP
  obtain ⟨hInject,_⟩ := order9_ten_distinct_prefix ha ho hN hM
  change Function.Bijective (fun i : Fin 10 => lowStateAt A (lowPrefix10 i)) at hInject
  let c := nodes A ∘ lowPrefix10
  let B := prefixMat10 A
  let w := gatherRow d.rep b
  let L := lateResidual B c w
  have haB : ∀i j,i≤j → B i j=0 := prefixMat10_strict ha
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
  have hInjectOn {i j : Fin 10} (hi : g A (lowPrefix10 i)=0)
      (hj : g A (lowPrefix10 j)=0) (h : c i=c j) : i=j :=
    hInject.1 (lowState_eq_iff.mpr ⟨by rw [hi,hj],h⟩)
  have hZeroD : g A (lowPrefix10 0)=0 := origin_zeroSpace ha 2 (mDef_mem A 1)
  have hZeroC : c 0=0 := by
    change (∑ j,A (0:Fin 12) j*1)=0
    exact Finset.sum_eq_zero fun j _=>by rw [ha 0 j (Fin.zero_le _),zero_mul]
  have hU0 : u≠0 := fun h => (by decide : iU≠0) (hInjectOn hUOn hZeroD (h.trans hZeroC.symm))
  have hV0 : v≠0 := fun h => (by decide : iV≠0) (hInjectOn hVOn hZeroD (h.trans hZeroC.symm))
  have huv : u≠v := fun h => (by decide : iU≠iV) (hInjectOn hUOn hVOn h)
  have onWitness (x : K) (hx : x∈cleanKnots A) :
      ∃ i : Fin 10, g A (lowPrefix10 i)=0 ∧ c i=x := by
    obtain ⟨j,hj,rfl⟩ := mem_cleanKnots.mp hx
    obtain ⟨i,hi⟩ := hInject.2 (lowStateAt A j)
    obtain ⟨hg,hc⟩ := lowState_eq_iff.mp hi
    exact ⟨i,hg.mpr hj,hc⟩
  let S : Finset K := (cleanKnots A).erase 0
  have hSc : S.card=4 := by
    have h := Finset.card_erase_add_one (zero_mem_cleanKnots ha : (0:K)∈cleanKnots A)
    change S.card+1=(cleanKnots A).card at h
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
  obtain ⟨_,eU,eR⟩ := RKCert.Paired.fixedRadau_late_column_equations u v r _ _ _ _ _ _
    d.nu d.alpha d.beta d.gamma huv hVn (d.psi_nonzero iU) (d.psi_nonzero iV) d.nu_nonzero
    hV1 hV2 hU2
    (hTriple iU (fun j hj => Or.inr (Or.inr (congrArg c (hOnlyV j hj)))))
    (hTriple iV (fun j hj => False.elim ((not_lt_of_ge (Fin.le_last j)) hj)))
    (hTriple ir hAfter)
  have hOff : ∀ x∈offKnots A, offMass A b x=0 :=
    fun x hx => offMass_zero_of_head ho hP (by omega) x hx
  obtain ⟨TZ,hTZ,normB⟩ := order9_on_quadrature_weight_norm (s:=11) ha ho hM hOff
  obtain ⟨SZ,normPsi⟩ := d.normPsi
  let q (i : Fin 10) := RKCert.Paired.nodalSlope (cleanKnots A) (c i)
  have hQB (i : Fin 10) (hi : g A (lowPrefix10 i)=0) (hc : c i≠0) :
      w i*q i*RKCert.Paired.fixedRadauT3 (c i)=TZ := by
    change gatherRow d.rep b i * _ * _ = _
    rw [d.on_b i hi]
    exact normB _ (mem_cleanKnots.mpr ⟨_,hi,rfl⟩) hc
  obtain ⟨hFF,hGG⟩ := RKCert.Paired.fixedRadau_FG_of_late_weights u v r _ _ _ _ _ _ d.nu
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
  have hFQ : RKCert.Paired.fixedRadauF u v Q=0 := by
    have hEq : RKCert.Paired.fixedRadauF u v P.eval=a*RKCert.Paired.fixedRadauF u v Q := by
      simp only [RKCert.Paired.fixedRadauF,hs,Q]; ring
    rw [hFF] at hEq
    exact (mul_eq_zero.mp hEq.symm).resolve_left ha0
  have hGQ : RKCert.Paired.fixedRadauG r u v Q=0 := by
    have hEq : RKCert.Paired.fixedRadauG r u v P.eval=a*RKCert.Paired.fixedRadauG r u v Q := by
      simp only [RKCert.Paired.fixedRadauG,hs,Q]; ring
    rw [hGG] at hEq
    exact (mul_eq_zero.mp hEq.symm).resolve_left ha0
  have hRad := order9_nodal_radau (s:=11) ha ho hM hOff
  have hRoot (i : Fin 10) (hi : g A (lowPrefix10 i)=0) (hc : c i≠0) :
      RKCert.Paired.radauQuartic.eval (c i)=0 :=
    radau_on_root hRad (mem_cleanKnots.mpr ⟨_,hi,rfl⟩) hc
  have rootW : ∀ i, RKCert.Paired.radauQuartic.eval (W i)=0 := by
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
  exact RKCert.Paired.fixedRadau_late_scalar_gate W s rootW injW hFQ hGQ


omit [CharZero K] in
/-- All remaining short explicit tableaux lie in the real (5,6)
atlas, with no extra rank or multiplicity premises. -/
theorem order9_five_six_remaining [LinearOrder K] [IsStrictOrderedRing K]
    {A : Matrix (Fin 12) (Fin 12) K} {b : Fin 12→K}
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder A b 9) :
    (offKnots A).card=5 ∧ (cleanKnots A).card=6 := by
  obtain ⟨off,on⟩ := order9_exactly_five_off ha ho
  exact ⟨off,on.resolve_left (order9_no_five_off_five_on ha ho off)⟩
omit [CharZero K] in
theorem explicit_order_nine_outside_five_six_at_least_thirteen [LinearOrder K] [IsStrictOrderedRing K]
    {m : ℕ} {A : Matrix (Fin m) (Fin m) K} {b : Fin m→K}
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder A b 9)
    (outside : ¬ ((offKnots A).card=5 ∧ (cleanKnots A).card=6)) : 13≤m := by
  by_contra! cap
  have size := (order9_forward_chart ha ho (by omega)).1
  subst m
  exact outside (order9_five_six_remaining ha ho)

end RKResearch.Certified.Graded.MultiOff
