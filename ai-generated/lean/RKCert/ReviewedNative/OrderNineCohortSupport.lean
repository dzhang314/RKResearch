module
public import RKCert.ReviewedNative.OrderNineCohortGeometry

@[expose] public section

/-! # Cohort support on every physical clock of the native five-off chart -/
namespace RKResearch.Certified.Graded.MultiOff
open RKResearch Module Polynomial OneOff Reverse RKCert.Endpoint
open scoped Matrix Classical
variable {K : Type*} [Field K] {s p : ℕ}

theorem row_polynomial_to_weights {A : Matrix (Fin s) (Fin s) K} (w : (Fin s→K)) (Q : K[X]) :
    row w (evalNodes A Q) =
      (∑ x∈cleanKnots A, onWeight A w x*Q.eval x) +
      (∑ x∈offKnots A, offMass A w x*Q.eval x) := by
  have he (i : Fin s) : w i*Q.eval (nodes A i) =
      (if OneOff.g A i=0 then w i*Q.eval (nodes A i) else 0) +
      (if OneOff.g A i≠0 then w i*Q.eval (nodes A i) else 0) := by
    by_cases h : OneOff.g A i=0 <;> simp [h]
  simp only [row_apply,dotProduct,evalNodes_apply]
  rw [Finset.sum_congr rfl (fun i _ => he i),Finset.sum_add_distrib,
    RKCert.Paired.sum_tagged_fibers w (nodes A) (fun i => OneOff.g A i=0) Q.eval,
    RKCert.Paired.sum_tagged_fibers w (nodes A) (fun i => OneOff.g A i≠0) Q.eval]
  rfl

theorem row_defect_to_off_weights {A : Matrix (Fin s) (Fin s) K} (w : (Fin s→K))
    (P Q : K[X]) (hP : ∀ i, OneOff.g A i≠0 → P.eval (nodes A i)=OneOff.g A i) :
    row w (diag (OneOff.g A) (evalNodes A Q)) =
      ∑ x∈offKnots A, offMass A w x*(P.eval x*Q.eval x) := by
  let f (x : K) := P.eval x*Q.eval x
  have he (i : Fin s) : w i*(OneOff.g A i*Q.eval (nodes A i)) =
      if OneOff.g A i≠0 then w i*f (nodes A i) else 0 := by
    by_cases h : OneOff.g A i=0 <;> simp [h,f,hP i]
  simp only [row_apply,dotProduct,diag_apply,evalNodes_apply]
  rw [Finset.sum_congr rfl (fun i _ => he i),
    RKCert.Paired.sum_tagged_fibers w (nodes A) (fun i => OneOff.g A i≠0) f]
  rfl

theorem row_of_all_weights_zero {A : Matrix (Fin s) (Fin s) K} {w : (Fin s→K)}
    (ho : ∀ x∈offKnots A, offMass A w x=0)
    (hn : ∀ x∈cleanKnots A, onWeight A w x=0) : w∈annih (onOffSpace A) := by
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
    {A : Matrix (Fin 12) (Fin 12) K} {b : (Fin 12→K)} (ha : ∀i j,i≤j → A i j=0)
    (ho : HasOrder A b 9)
    (hN : (offKnots A).card=5) (hM : (cleanKnots A).card=5)
    {P : K[X]} (hPd : P.natDegree≤2)
    (hF : zeroSpace A 4=band A 2)
    (hP : ∀ i, OneOff.g A i≠0 → P.eval (nodes A i)=OneOff.g A i) :
    ∀ x∈cleanKnots A, P.eval x≠0 := by
  have hoff : ∀ x∈offKnots A, offMass A b x=0 :=
    fun x hx => offMass_zero_of_head ho hP (by omega) x hx
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
  have hz' : evalNodes A Q+diag (OneOff.g A) (evalNodes A R)=0 := hz
  let S := cleanKnots A
  let T := offKnots A
  let H := nodalHull S
  let J := nodalHull T
  obtain ⟨a,ha'⟩ := RKCert.Paired.polynomial_scalar_hull S Q (hQd.trans_eq hM.symm) (fun x hx => by
    obtain ⟨i,hi,rfl⟩ := mem_cleanKnots.mp hx
    exact profile_on_eval Q R hz' hi)
  obtain ⟨c,hc⟩ := RKCert.Paired.polynomial_scalar_hull T (Q+P*R)
    ((natDegree_add_le_of_degree_le hQd (natDegree_mul_le_of_le hPd hRd)).trans_eq hN.symm)
    (fun x hx => by
      obtain ⟨i,hi,rfl⟩ := mem_offKnots.mp hx
      exact profile_off_eval hz' hP hi)
  have ha0 : a≠0 := by
    intro he
    have hQ : Q=0 := by simp [ha',he]
    have hR := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' R T (fun x hx => by
      obtain ⟨i,hi,rfl⟩ := mem_offKnots.mp hx
      have h := congrFun hz' i
      change Q.eval (nodes A i)+OneOff.g A i*R.eval (nodes A i)=0 at h
      exact (mul_eq_zero.mp (by simpa [hQ] using h)).resolve_left hi) (hRd.trans_lt (by change 3 < (offKnots A).card; omega))
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
    exact RKCert.Paired.nodalHull_eval_ne_zero_of_notMem hmem ((mul_eq_zero.mp h.symm).resolve_left hc0)
  obtain ⟨i,hi,he⟩ := mem_offKnots.mp hxT
  exact hi ((hP i hi).symm.trans (he.symm ▸ hv))

omit [CharZero K] in
/-- A nonzero state-level row killing E5 has nonzero aggregates
at all five on and all five off features. -/
theorem fifth_profile_annih_full_state_support {A : Matrix (Fin s) (Fin s) K}
    {w : (Fin s→K)} (hw : w∈annih (treeSpace A 5)) (hW : w∉annih (onOffSpace A))
    (hN : (offKnots A).card=5) (hM : (cleanKnots A).card=5)
    {P : K[X]} (hPd : P.natDegree≤2)
    (hP : ∀ i, OneOff.g A i≠0 → P.eval (nodes A i)=OneOff.g A i)
    (hO : ∀ x∈cleanKnots A, P.eval x≠0) :
    (∀ x∈cleanKnots A, onWeight A w x≠0) ∧
      (∀ x∈offKnots A, offMass A w x≠0) := by
  let S := cleanKnots A
  let T := offKnots A
  have hcS : S.card=5 := hM
  have hcT : T.card=5 := hN
  let f (x : K) := onWeight A w x*P.eval x
  let g (x : K) := offMass A w x*P.eval x
  have hz (x : K) (hx : x∈T) : P.eval x≠0 := by
    obtain ⟨i,hi,rfl⟩ := mem_offKnots.mp hx
    rwa [hP i hi]
  have hg (Q : K[X]) (hd : Q.natDegree≤3) : ∑ x∈T,g x*Q.eval x=0 := by
    have hv : diag (OneOff.g A) (evalNodes A Q)∈treeSpace A 5 := by
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
    have hOff (x : K) (hx : x∈T) : offMass A w x=0 :=
      (mul_eq_zero.mp (ha x hx)).resolve_right (hz x hx)
    have hOn := RKCert.Paired.weight_zero_by_full_interpolation S (onWeight A w) (fun Q hd => by
      have he := mem_annih.mp hw _ (evalNodes_mem_treeSpace A Q (by omega : Q.natDegree≤5))
      rw [row_polynomial_to_weights] at he
      have hSum : (∑ x∈T,offMass A w x*Q.eval x)=0 :=
        Finset.sum_eq_zero fun x hx => by rw [hOff x hx,zero_mul]
      change _+(∑ x∈T,offMass A w x*Q.eval x)=0 at he
      rwa [hSum,add_zero] at he)
    exact hW (row_of_all_weights_zero hOff hOn)
  have hnF : ∃ x∈S,f x≠0 := by
    by_contra! ha
    have hOn (x : K) (hx : x∈S) : onWeight A w x=0 :=
      (mul_eq_zero.mp (ha x hx)).resolve_right (hO x hx)
    have hOff := RKCert.Paired.weight_zero_by_full_interpolation T (offMass A w) (fun Q hd => by
      have he := mem_annih.mp hw _ (evalNodes_mem_treeSpace A Q (by omega : Q.natDegree≤5))
      rw [row_polynomial_to_weights] at he
      have hSum : (∑ x∈S,onWeight A w x*Q.eval x)=0 :=
        Finset.sum_eq_zero fun x hx => by rw [hOn x hx,zero_mul]
      change (∑ x∈S,onWeight A w x*Q.eval x)+_=0 at he
      rwa [hSum,zero_add] at he)
    exact hW (row_of_all_weights_zero hOff hOn)
  constructor
  · intro x hx h
    exact RKCert.Paired.weight_full_support_of_five S f hcS hf hnF x hx (by simp [f,h])
  · intro x hx h
    exact RKCert.Paired.weight_full_support_of_five T g hcT hg hnG x hx (by simp [g,h])

omit [CharZero K] in
theorem stage_before_of_tagged_weight_nonzero (w c : (Fin s→K)) (j : Fin s)
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
theorem earlier_states_surjective {A : Matrix (Fin s) (Fin s) K} {w : (Fin s→K)} (j : Fin s)
    (hW : ∀ i, j ≤ i → w i=0)
    (hOn : ∀ x∈cleanKnots A, onWeight A w x≠0)
    (hOff : ∀ x∈offKnots A, offMass A w x≠0) :
    Function.Surjective (fun i : Fin j.val => lowStateAt A (Fin.castLE j.isLt.le i)) := by
  intro z
  rcases z with a|a
  · obtain ⟨i,hi,hg,hc⟩ := stage_before_of_tagged_weight_nonzero w (nodes A) j hW
      (fun i => OneOff.g A i=0) a.val (hOn a.val a.property)
    refine ⟨⟨i.val,hi⟩,?_⟩
    change lowStateAt A i=Sum.inl a
    simp [lowStateAt,hg,hc]
  · obtain ⟨i,hi,hg,hc⟩ := stage_before_of_tagged_weight_nonzero w (nodes A) j hW
      (fun i => OneOff.g A i≠0) a.val (hOff a.val a.property)
    refine ⟨⟨i.val,hi⟩,?_⟩
    change lowStateAt A i=Sum.inr a
    simp [lowStateAt,hg,hc]

/-- The repeated reverse-contrast row is exactly chronological stage
eleven, and the prefix of ten stages represents all ten states. -/
theorem order9_ten_distinct_prefix_full
    {A : Matrix (Fin 12) (Fin 12) K} {b : (Fin 12→K)} (ha : ∀i j,i≤j → A i j=0)
    (ho : HasOrder A b 9)
    (hN : (offKnots A).card=5) (hM : (cleanKnots A).card=5) :
    Function.Bijective (fun i : Fin 10 => lowStateAt A (Fin.castLE (by decide) i)) ∧
      (∃ i : Fin 12, i < (10:Fin 12) ∧ lowStateAt A i=lowStateAt A (10:Fin 12) ∧
        ∃ a : K, a≠0 ∧
          orderAdjoint A b 1 = a • (Pi.single i 1-Pi.single (10:Fin 12) 1)) ∧
      (∀ x∈cleanKnots A, onWeight A (transMat A (orderAdjoint A b 1)) x≠0) ∧
      (∀ x∈offKnots A, offMass A (transMat A (orderAdjoint A b 1)) x≠0) := by
  obtain ⟨P,hPd,_,_,hF,hP⟩ := order9_two_curve_head ha ho (by decide) (by omega)
  have hO := order9_five_on_off_head_nonzero_on ha ho hN hM hPd hF hP
  obtain ⟨hE6,hS6⟩ := order9_five_on_off_stage_six_split ha ho hN hM
  obtain ⟨i,j,hij,hjl,hstate,a,ha0,he,hNe⟩ :=
    order9_five_on_off_reverse_contrast ha ho hN hM
  let r := orderAdjoint A b 1
  let w := transMat A r
  have hr := orderAdjoint_annih ho (j:=6) (k:=1) (by decide)
  have hw : w∈annih (treeSpace A 5) := annih_map_transpose (mat_treeSpace A 5) (Submodule.mem_map_of_mem hr)
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
      have e := finrank_annih (treeSpace A 6); rw [Fintype.card_fin] at e; omega
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
    {A : Matrix (Fin 12) (Fin 12) K} {b : (Fin 12→K)} (ha : ∀i j,i≤j → A i j=0)
    (ho : HasOrder A b 9)
    (hN : (offKnots A).card=5) (hM : (cleanKnots A).card=5) :
    Function.Bijective (fun i : Fin 10 => lowStateAt A (Fin.castLE (by decide) i)) ∧
      ∃ i : Fin 12, i < (10:Fin 12) ∧ lowStateAt A i=lowStateAt A (10:Fin 12) ∧
        ∃ a : K, a≠0 ∧
          orderAdjoint A b 1 = a • (Pi.single i 1-Pi.single (10:Fin 12) 1) := by
  have h := order9_ten_distinct_prefix_full ha ho hN hM
  exact ⟨h.1,h.2.1⟩
end RKResearch.Certified.Graded.MultiOff
