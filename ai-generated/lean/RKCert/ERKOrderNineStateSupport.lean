module

public import RKCert.ERKOrderNineLatePrefix
public import RKCert.RadauPhysicalNondivisibility

@[expose] public section

/-! # Full-support state rows in the fixed-Radau branch -/
namespace RKCert.Paired
open Module Polynomial RKCert.Endpoint RKCert.FixedFactor
open scoped Classical

variable {K : Type*} [Field K] {s : ℕ}

theorem nodalHull_dvd_of_roots (S : Finset K) (P : K[X])
    (h : ∀ x∈S, P.eval x=0) : nodalHull S∣P := by
  unfold nodalHull
  apply Finset.prod_dvd_of_coprime
  · intro a _ b _ hn
    exact isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hn).isUnit
  · intro a ha; exact dvd_iff_isRoot.mpr (h a ha)

theorem polynomial_scalar_hull (S : Finset K) (P : K[X]) (hd : P.natDegree≤S.card)
    (h : ∀ x∈S, P.eval x=0) : ∃ a : K, P=C a*nodalHull S := by
  obtain ⟨R,he⟩ := nodalHull_dvd_of_roots S P h
  by_cases hR : R=0
  · exact ⟨0,by simp [he,hR]⟩
  · have hdeg := natDegree_mul (monic_nodalHull S).ne_zero hR
    rw [←he,natDegree_nodalHull] at hdeg
    have hc : R=C (R.coeff 0) := eq_C_of_natDegree_eq_zero (by omega)
    exact ⟨R.coeff 0,by rw [he,hc,mul_comm,coeff_C_zero]⟩

theorem weight_zero_by_full_interpolation (S : Finset K) (w : K → K)
    (h : ∀ P : K[X], P.natDegree < S.card → ∑ x∈S,w x*P.eval x=0) :
    ∀ x∈S, w x=0 := by
  intro x hx
  let f (y : K) := if y=x then (1:K) else 0
  let P := Lagrange.interpolate S id f
  have hd : P.natDegree < S.card := by
    by_cases hP : P=0
    · rw [hP,natDegree_zero]; exact Finset.card_pos.mpr ⟨x,hx⟩
    · exact (natDegree_lt_iff_degree_lt hP).mpr
        (Lagrange.degree_interpolate_lt f (Set.injOn_id _))
  have hP (y) (hy : y∈S) : P.eval y=f y :=
    Lagrange.eval_interpolate_at_node f (Set.injOn_id _) hy
  have he := h P hd
  rw [Finset.sum_eq_single x] at he
  · simpa [hP x hx,f] using he
  · intro y hy hne; simp [hP y hy,f,hne]
  · intro hn; exact False.elim (hn hx)

theorem weight_full_support_of_five (S : Finset K) (w : K → K) (hc : S.card=5)
    (hm : ∀ P : K[X], P.natDegree≤3 → ∑ x∈S,w x*P.eval x=0)
    (hne : ∃ x∈S, w x≠0) :
    ∀ x∈S, w x≠0 := by
  intro x hx h0
  let T := S.erase x
  have hT : T.card+1=S.card := Finset.card_erase_add_one hx
  have hW := weight_zero_by_full_interpolation T w (fun P hp => by
    have h := hm P (by omega)
    have he := Finset.sum_erase_add S (fun y => w y*P.eval y) hx
    rw [h0,zero_mul,add_zero,h] at he
    exact he)
  obtain ⟨y,hy,hy0⟩ := hne
  by_cases h : y=x
  · exact hy0 (h.symm ▸ h0)
  · exact hy0 (hW y (Finset.mem_erase.mpr ⟨h,hy⟩))

theorem row_polynomial_to_weights {A : Fin s → Fin s → K} (w : Vec K s) (Q : K[X]) :
    row w (evalNodes A Q) =
      (∑ x∈onNodes A, onWeight A w x*Q.eval x) +
      (∑ x∈supportedNodes A (qdef A), offWeight A w x*Q.eval x) := by
  have he (i : Fin s) : w i*Q.eval (nodes A i) =
      (if qdef A i=0 then w i*Q.eval (nodes A i) else 0) +
      (if qdef A i≠0 then w i*Q.eval (nodes A i) else 0) := by
    by_cases h : qdef A i=0 <;> simp [h]
  simp only [row_apply,evalNodes_apply]
  rw [Finset.sum_congr rfl (fun i _ => he i),Finset.sum_add_distrib,
    sum_tagged_fibers w (nodes A) (fun i => qdef A i=0) Q.eval,
    sum_tagged_fibers w (nodes A) (fun i => qdef A i≠0) Q.eval]
  rfl

theorem row_defect_to_off_weights {A : Fin s → Fin s → K} (w : Vec K s)
    (P Q : K[X]) (hP : ∀ i, qdef A i≠0 → P.eval (nodes A i)=qdef A i) :
    row w (diag (qdef A) (evalNodes A Q)) =
      ∑ x∈supportedNodes A (qdef A), offWeight A w x*(P.eval x*Q.eval x) := by
  let f (x : K) := P.eval x*Q.eval x
  have he (i : Fin s) : w i*(qdef A i*Q.eval (nodes A i)) =
      if qdef A i≠0 then w i*f (nodes A i) else 0 := by
    by_cases h : qdef A i=0 <;> simp [h,f,hP i]
  simp only [row_apply,diag_apply,evalNodes_apply]
  rw [Finset.sum_congr rfl (fun i _ => he i),
    sum_tagged_fibers w (nodes A) (fun i => qdef A i≠0) f]
  rfl

theorem row_of_all_weights_zero {A : Fin s → Fin s → K} {w : Vec K s}
    (ho : ∀ x∈supportedNodes A (qdef A), offWeight A w x=0)
    (hn : ∀ x∈onNodes A, onWeight A w x=0) : w∈annih (onOffSpace A) := by
  apply mem_annih.mpr
  rintro _ ⟨z,rfl⟩
  have h : diag (evalNodes A (1:K[X])) (onOffEval A z)=onOffEval A z := by ext i; simp
  rw [←h,row_onOff_eval_eq_onWeights ho]
  exact Finset.sum_eq_zero (fun x hx => by rw [hn x hx,zero_mul])

variable [CharZero K]

/-- The literal fifth-profile kernel forces the quadratic/linear head to
be nonzero at every on state as well; this uses the actual Radau divisor
certificate rather than any assumption about cross-curve coincidences. -/
theorem order9_five_on_off_head_nonzero_on
    {A : Fin 12 → Fin 12 → K} {b : Vec K 12} (ha : StrictLower A)
    (ho : HasTreeOrderAtLeast A b 9)
    (hN : (supportedNodes A (qdef A)).card=5) (hM : (onNodes A).card=5)
    {P : K[X]} (hPd : P.natDegree≤2)
    (hF : zeroSpace A 4=chainSpan A (qdef A) 2)
    (hP : ∀ i, qdef A i≠0 → P.eval (nodes A i)=qdef A i) :
    ∀ x∈onNodes A, P.eval x≠0 := by
  have hoff : ∀ x∈supportedNodes A (qdef A), offWeight A b x=0 :=
    fun x hx => offWeight_eq_zero_from_head ho P hP (by omega) x hx
  have hnr := order9_five_on_head_not_dvd (s:=11) ha ho hM hoff hF P hPd hP
  obtain ⟨hr,_,_⟩ := order9_five_on_off_stage_five_split ha ho hN hM
  have hinj : ¬Function.Injective (gradeFiveStateMap A) := by
    intro hf
    have hd := LinearMap.finrank_range_of_inj hf
    change finrank K (gradeFiveStateSpace A) = finrank K ((Fin 6 → K) × (Fin 4 → K)) at hd
    rw [hr,Module.finrank_prod,Module.finrank_fin_fun,Module.finrank_fin_fun] at hd
    omega
  have h0 := mt (injective_iff_map_eq_zero (gradeFiveStateMap A)).mpr hinj
  push Not at h0
  obtain ⟨z,hz,hzn⟩ := h0
  let Q := ofFn 6 z.1
  let R := ofFn 4 z.2
  have hQd : Q.natDegree≤5 := Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) _)
  have hRd : R.natDegree≤3 := Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) _)
  rw [gradeFiveStateMap_eq_eval] at hz
  have hz' : evalNodes A Q+diag (qdef A) (evalNodes A R)=0 := hz
  let S := onNodes A
  let T := supportedNodes A (qdef A)
  let H := nodalHull S
  let J := nodalHull T
  obtain ⟨a,ha'⟩ := polynomial_scalar_hull S Q (hQd.trans_eq hM.symm) (fun x hx => by
    obtain ⟨i,hi,rfl⟩ := mem_onNodes.mp hx
    exact profile_on_eval Q R hz' hi)
  obtain ⟨c,hc⟩ := polynomial_scalar_hull T (Q+P*R)
    ((natDegree_add_le_of_degree_le hQd (natDegree_mul_le_of_le hPd hRd)).trans_eq hN.symm)
    (fun x hx => by
      obtain ⟨i,hi,rfl⟩ := mem_supportedNodes.mp hx
      exact profile_off_eval hz' hP hi)
  have ha0 : a≠0 := by
    intro he
    have hQ : Q=0 := by simp [ha',he]
    have hR := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' R T (fun x hx => by
      obtain ⟨i,hi,rfl⟩ := mem_supportedNodes.mp hx
      have h := congrFun hz' i
      change Q.eval (nodes A i)+qdef A i*R.eval (nodes A i)=0 at h
      exact (mul_eq_zero.mp (by simpa [hQ] using h)).resolve_left hi) (hRd.trans_lt (by change 3 < (supportedNodes A (qdef A)).card; omega))
    exact hzn (Prod.ext (injective_ofFn 6 (hQ.trans (ofFn_zero _).symm))
      (injective_ofFn 4 (hR.trans (ofFn_zero _).symm)))
  have hc0 : c≠0 := by
    intro he
    have hEq : Q+P*R=0 := by simp [hc,he]
    have hQ : C a*H = P*(-R) := by
      rw [mul_neg,eq_neg_iff_add_eq_zero,←show Q=C a*H from ha']; exact hEq
    apply hnr
    refine ⟨C a⁻¹*(-R),?_⟩
    calc
      H = C a⁻¹*(C a*H) := by rw [←mul_assoc,←map_mul,inv_mul_cancel₀ ha0,map_one,one_mul]
      _ = _ := by rw [hQ]; ring
  intro x hx hv
  have h := congrArg (fun V : K[X] => V.eval x) hc
  have hQ : Q.eval x=0 := by rw [ha',eval_mul,nodalHull_eval_of_mem hx,mul_zero]
  rw [eval_add,eval_mul,hQ,hv,zero_mul,add_zero,eval_mul,eval_C] at h
  have hxT : x∈T := by
    by_contra hmem
    exact nodalHull_eval_ne_zero_of_notMem hmem ((mul_eq_zero.mp h.symm).resolve_left hc0)
  obtain ⟨i,hi,he⟩ := mem_supportedNodes.mp hxT
  exact hi ((hP i hi).symm.trans (he.symm ▸ hv))

/-- A nonzero state-level row killing E5 has nonzero aggregates
at all five on and all five off features. -/
theorem fifth_profile_annih_full_state_support {A : Fin s → Fin s → K}
    {w : Vec K s} (hw : w∈annih (treeSpace A 5)) (hW : w∉annih (onOffSpace A))
    (hN : (supportedNodes A (qdef A)).card=5) (hM : (onNodes A).card=5)
    {P : K[X]} (hPd : P.natDegree≤2)
    (hP : ∀ i, qdef A i≠0 → P.eval (nodes A i)=qdef A i)
    (hO : ∀ x∈onNodes A, P.eval x≠0) :
    (∀ x∈onNodes A, onWeight A w x≠0) ∧
      (∀ x∈supportedNodes A (qdef A), offWeight A w x≠0) := by
  let S := onNodes A
  let T := supportedNodes A (qdef A)
  have hcS : S.card=5 := hM
  have hcT : T.card=5 := hN
  let f (x : K) := onWeight A w x*P.eval x
  let g (x : K) := offWeight A w x*P.eval x
  have hz (x : K) (hx : x∈T) : P.eval x≠0 := by
    obtain ⟨i,hi,rfl⟩ := mem_supportedNodes.mp hx
    rwa [hP i hi]
  have hg (Q : K[X]) (hd : Q.natDegree≤3) : ∑ x∈T,g x*Q.eval x=0 := by
    have hv : diag (qdef A) (evalNodes A Q)∈treeSpace A 5 := by
      have h := pairProfile_mem_E5 A (0:K[X]) Q (by simp) hd
      have he : evalNodes A (0:K[X])=0 := by ext i; simp
      rwa [he,zero_add] at h
    have he := mem_annih.mp hw _ hv
    rw [row_defect_to_off_weights w P Q hP] at he
    simpa only [g,mul_assoc] using he
  have hf (Q : K[X]) (hd : Q.natDegree≤3) : ∑ x∈S,f x*Q.eval x=0 := by
    have he := mem_annih.mp hw _ (evalNodes_mem_treeSpace A (P*Q)
      (natDegree_mul_le_of_le hPd hd))
    rw [row_polynomial_to_weights] at he
    simp only [eval_mul,← mul_assoc] at he
    change (∑ x∈S,f x*Q.eval x) + (∑ x∈T,g x*Q.eval x)=0 at he
    rwa [hg Q hd,add_zero] at he
  have hnG : ∃ x∈T,g x≠0 := by
    by_contra! ha
    have hOff (x : K) (hx : x∈T) : offWeight A w x=0 :=
      (mul_eq_zero.mp (ha x hx)).resolve_right (hz x hx)
    have hOn := weight_zero_by_full_interpolation S (onWeight A w) (fun Q hd => by
      have he := mem_annih.mp hw _ (evalNodes_mem_treeSpace A Q (by omega : Q.natDegree≤5))
      rw [row_polynomial_to_weights] at he
      have hSum : (∑ x∈T,offWeight A w x*Q.eval x)=0 :=
        Finset.sum_eq_zero fun x hx => by rw [hOff x hx,zero_mul]
      change _+(∑ x∈T,offWeight A w x*Q.eval x)=0 at he
      rwa [hSum,add_zero] at he)
    exact hW (row_of_all_weights_zero hOff hOn)
  have hnF : ∃ x∈S,f x≠0 := by
    by_contra! ha
    have hOn (x : K) (hx : x∈S) : onWeight A w x=0 :=
      (mul_eq_zero.mp (ha x hx)).resolve_right (hO x hx)
    have hOff := weight_zero_by_full_interpolation T (offWeight A w) (fun Q hd => by
      have he := mem_annih.mp hw _ (evalNodes_mem_treeSpace A Q (by omega : Q.natDegree≤5))
      rw [row_polynomial_to_weights] at he
      have hSum : (∑ x∈S,onWeight A w x*Q.eval x)=0 :=
        Finset.sum_eq_zero fun x hx => by rw [hOn x hx,zero_mul]
      change (∑ x∈S,onWeight A w x*Q.eval x)+_=0 at he
      rwa [hSum,zero_add] at he)
    exact hW (row_of_all_weights_zero hOff hOn)
  constructor
  · intro x hx h
    exact weight_full_support_of_five S f hcS hf hnF x hx (by simp [f,h])
  · intro x hx h
    exact weight_full_support_of_five T g hcT hg hnG x hx (by simp [g,h])

omit [CharZero K] in
theorem stage_before_of_tagged_weight_nonzero (w c : Vec K s) (j : Fin s)
    (hW : ∀ k, j ≤ k → w k=0) (tag : Fin s → Prop) [DecidablePred tag] (x : K)
    (hn : (∑ i, if tag i ∧ c i=x then w i else 0)≠0) :
    ∃ i, i < j ∧ tag i ∧ c i=x := by
  by_contra! H
  apply hn
  apply Finset.sum_eq_zero
  intro i _
  by_cases h : tag i ∧ c i=x
  · rw [ite_eq_left h,hW i (le_of_not_gt fun hi => H i hi h.1 h.2)]
  · simp [h]

omit [CharZero K] in
theorem earlier_states_surjective {A : Fin s → Fin s → K} {w : Vec K s} (j : Fin s)
    (hW : ∀ i, j ≤ i → w i=0)
    (hOn : ∀ x∈onNodes A, onWeight A w x≠0)
    (hOff : ∀ x∈supportedNodes A (qdef A), offWeight A w x≠0) :
    Function.Surjective (fun i : Fin j.val => lowStateAt A (Fin.castLE j.isLt.le i)) := by
  intro z
  rcases z with a|a
  · obtain ⟨i,hi,hg,hc⟩ := stage_before_of_tagged_weight_nonzero w (nodes A) j hW
      (fun i => qdef A i=0) a.val (hOn a.val a.property)
    refine ⟨⟨i.val,hi⟩,?_⟩
    change lowStateAt A i=Sum.inl a
    simp [lowStateAt,hg,hc]
  · obtain ⟨i,hi,hg,hc⟩ := stage_before_of_tagged_weight_nonzero w (nodes A) j hW
      (fun i => qdef A i≠0) a.val (hOff a.val a.property)
    refine ⟨⟨i.val,hi⟩,?_⟩
    change lowStateAt A i=Sum.inr a
    simp [lowStateAt,hg,hc]

/-- The repeated reverse-contrast row is exactly chronological stage
eleven, and the prefix of ten stages represents all ten states. -/
theorem order9_ten_distinct_prefix_full
    {A : Fin 12 → Fin 12 → K} {b : Vec K 12} (ha : StrictLower A)
    (ho : HasTreeOrderAtLeast A b 9)
    (hN : (supportedNodes A (qdef A)).card=5) (hM : (onNodes A).card=5) :
    Function.Bijective (fun i : Fin 10 => lowStateAt A (Fin.castLE (by decide) i)) ∧
      (∃ i : Fin 12, i < (10:Fin 12) ∧ lowStateAt A i=lowStateAt A (10:Fin 12) ∧
        ∃ a : K, a≠0 ∧
          orderAdjoint A b 1 = a • (Pi.single i 1-Pi.single (10:Fin 12) 1)) ∧
      (∀ x∈onNodes A, onWeight A (transMat A (orderAdjoint A b 1)) x≠0) ∧
      (∀ x∈supportedNodes A (qdef A), offWeight A (transMat A (orderAdjoint A b 1)) x≠0) := by
  obtain ⟨_,h3,h4,_,_,_,_,_⟩ := order9_twelve_stage_chart ha ho
  obtain ⟨P,hPd,_,_,hF,hP⟩ := two_curve_head h3 h4 (by omega)
  have hO := order9_five_on_off_head_nonzero_on ha ho hN hM hPd hF hP
  obtain ⟨hE6,hS6⟩ := order9_five_on_off_stage_six_split ha ho hN hM
  obtain ⟨i,j,hij,hjl,hstate,a,ha0,he,hNe⟩ :=
    order9_five_on_off_reverse_contrast ha ho hN hM
  let r := orderAdjoint A b 1
  let w := transMat A r
  have hr := orderAdjoint_annih ho (j:=6) (k:=1) (by decide)
  have hw : w∈annih (treeSpace A 5) := transMat_mem_annih_pred hr
  have hW (k : Fin 12) (hk : j≤k) : w k=0 := by
    change transMat A (orderAdjoint A b 1) k=0
    rw [he,map_smul,Pi.smul_apply,smul_eq_mul,map_sub,
      transMat_single_incoming_row,transMat_single_incoming_row,Pi.sub_apply,
      ha i k (hij.le.trans hk),ha j k hk,sub_self,mul_zero]
  have hn : w∉annih (onOffSpace A) := by
    intro hv
    have hA : w∈annih (treeSpace A 6) := by
      apply mem_annih.mpr
      rw [hS6]
      rintro v hv'
      obtain ⟨x,hx,y,hy,rfl⟩ := Submodule.mem_sup.mp hv'
      obtain ⟨m,rfl⟩ := Submodule.mem_span_singleton.mp hy
      rw [map_add,map_smul,mem_annih.mp hv x hx,row_single_eq_coord,hW _ hjl.le,smul_zero,add_zero]
    have hrj : r j=-a := by
      change orderAdjoint A b 1 j=-a
      rw [he]; simp [ne_of_gt hij]
    have hr' : r≠0 := by
      intro h; rw [h] at hrj; exact ha0 (neg_eq_zero.mp hrj.symm)
    have hAnn : finrank K (annih (treeSpace A 6))=1 := by
      have := finrank_add_annih_eq (treeSpace A 6); omega
    have hSpan : Submodule.span K {r}=annih (treeSpace A 6) :=
      Submodule.eq_of_le_of_finrank_le ((Submodule.span_singleton_le_iff_mem ..).mpr hr)
        (by rw [hAnn,finrank_span_singleton hr'])
    rw [←hSpan] at hA
    obtain ⟨t,ht⟩ := Submodule.mem_span_singleton.mp hA
    have hj := congrFun ht j
    change t*r j=w j at hj
    rw [hrj,hW j le_rfl] at hj
    have htz := (mul_eq_zero.mp hj).resolve_right (neg_ne_zero.mpr ha0)
    rw [htz,zero_smul] at ht
    exact hNe ht.symm
  obtain ⟨hOn,hOff⟩ := fifth_profile_annih_full_state_support hw hn hN hM hPd hP hO
  have hs := earlier_states_surjective j hW hOn hOff
  have hc := Fintype.card_le_of_surjective _ hs
  rw [lowState_card,Fintype.card_fin,hM,hN] at hc
  have hJ : j=(10:Fin 12) := by
    change j.val < 11 at hjl
    apply Fin.ext; change j.val=10; omega
  subst j
  have hs' : Function.Surjective (fun i : Fin 10 => lowStateAt A (Fin.castLE (by decide) i)) := hs
  have hbij := (Fintype.bijective_iff_surjective_and_card _).mpr
    ⟨hs',by rw [Fintype.card_fin,lowState_card,hM,hN]⟩
  exact ⟨hbij,⟨i,hij,hstate,a,ha0,he⟩,hOn,hOff⟩

theorem order9_ten_distinct_prefix
    {A : Fin 12 → Fin 12 → K} {b : Vec K 12} (ha : StrictLower A)
    (ho : HasTreeOrderAtLeast A b 9)
    (hN : (supportedNodes A (qdef A)).card=5) (hM : (onNodes A).card=5) :
    Function.Bijective (fun i : Fin 10 => lowStateAt A (Fin.castLE (by decide) i)) ∧
      ∃ i : Fin 12, i < (10:Fin 12) ∧ lowStateAt A i=lowStateAt A (10:Fin 12) ∧
        ∃ a : K, a≠0 ∧
          orderAdjoint A b 1 = a • (Pi.single i 1-Pi.single (10:Fin 12) 1) := by
  have h := order9_ten_distinct_prefix_full ha ho hN hM
  exact ⟨h.1,h.2.1⟩

end RKCert.Paired
