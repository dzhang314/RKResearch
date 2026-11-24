module
public import RKCert.ReviewedNative.OrderNineMultiFiveClean

@[expose] public section

/-! # Exclude six defective clocks over an ordered field -/
namespace RKResearch.Certified.Graded.MultiOff
open RKResearch Module Polynomial OneOff RKCert.Endpoint
open scoped Matrix Classical
variable {K : Type*} [Field K] [CharZero K] {s p : ℕ}

theorem first_nonzero_on_forces_head_shape {A : Matrix (Fin s) (Fin s) K}
    (ha : ∀i j,i≤j → A i j=0) (hF : zeroSpace A 4 = band A 2)
    {P : K[X]} (hd : P.natDegree ≤ 2) (hn : P ≠ 0)
    (hP : ∀ j, g A j ≠ 0 → P.eval (nodes A j) = g A j)
    (hex : ∃ i, g A i = 0 ∧ nodes A i ≠ 0) :
    P.eval 0 ≠ 0 ∧ 1 ≤ P.natDegree := by
  let U : Set (Fin s) := {i | g A i = 0 ∧ nodes A i ≠ 0}
  have hU : U.Nonempty := hex
  obtain ⟨i,hi,hmin⟩ := wellFounded_lt.has_min U hU
  rcases (show g A i=0 ∧ nodes A i≠0 from hi) with ⟨hdi,hni⟩
  let u := nodes A i
  change u ≠ 0 at hni
  have hzero (j : Fin s) (hj : j < i) (hj' : g A j=0) : nodes A j=0 := by
    by_contra h
    exact hmin j ⟨hj',h⟩ hj
  have hA : mat A (g A) i=0 := clean_four_vanish hF hdi
    (zeroSpace_mono A (by decide : 3≤4) (mat_zeroSpace_charZero A 2 (mDef_mem A 1)))
  have hAC := clean_mixed_defect hF hdi
  have hXd : (X*P).natDegree ≤ 3 := Polynomial.natDegree_mul_le_of_le (by simp) hd
  have hxP := on_primitive_zero_of_prefix ha hF hdi (X*P) hXd
    (diag (nodes A) (g A)) hAC (fun j hj => by
      by_cases hg : g A j=0
      · simp [hg,hzero j hj hg]
      · simp [hP j hg])
  rw [←scalar_primitive,RKCert.Paired.primitive_eval_X_quadratic P hd] at hxP
  change P.coeff 0*u^2/2 + P.coeff 1*u^3/3 + P.coeff 2*u^4/4 = 0 at hxP
  constructor
  · intro h
    have hz : P.coeff 0=0 := (coeff_zero_eq_eval_zero P).trans h
    have hP' := on_primitive_zero_of_prefix ha hF hdi P (by omega) (g A) hA
      (fun j hj => by
        by_cases hg : g A j=0
        · rw [hzero j hj hg,h,hg]
        · exact hP j hg)
    rw [←scalar_primitive,RKCert.Paired.primitive_eval_quadratic P hd] at hP'
    change P.coeff 0*u + P.coeff 1*u^2/2 + P.coeff 2*u^3/3 = 0 at hP'
    have hb : P.coeff 2 * u^4=0 := by linear_combination 36*hxP - 24*u*hP' + 6*u^2*hz
    have hb' := (mul_eq_zero.mp hb).resolve_right (pow_ne_zero _ hni)
    rw [hz,hb'] at hP'
    have h : P.coeff 1*u^2=0 := by linear_combination 2*hP'
    have ha' := (mul_eq_zero.mp h).resolve_right (pow_ne_zero _ hni)
    apply hn
    rw [RKCert.Paired.quadratic_coeff_expand P hd,hz,ha',hb']
    simp
  · by_contra! h
    have hC : P = C (P.coeff 0) := eq_C_of_natDegree_eq_zero (by omega)
    have h1 : P.coeff 1=0 := by nth_rw 1 [hC]; simp
    have h2 : P.coeff 2=0 := by nth_rw 1 [hC]; simp
    rw [h1,h2] at hxP
    have h0 : P.coeff 0*u^2=0 := by linear_combination 2*hxP
    have hp0 := (mul_eq_zero.mp h0).resolve_right (pow_ne_zero _ hni)
    exact hn (by rw [hC,hp0,map_zero])

theorem order9_six_on_pencil {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : (Fin (s+1)→K)}
    (ha : ∀i j,i≤j → A i j=0) (ho : HasOrder A b 9)
    (hM : (cleanKnots A).card=6) (h1 : (1:K)∈cleanKnots A)
    (hoff : ∀ x∈offKnots A, offMass A b x=0) :
    ∃ l : K, nodalHull (RKCert.Paired.endpointErase (RKCert.Paired.endpointErase (cleanKnots A) 1) 0)=RKCert.Paired.lobattoPencil l := by
  let S := RKCert.Paired.endpointErase (RKCert.Paired.endpointErase (cleanKnots A) 1) 0
  let H := nodalHull S
  have h0 := zero_mem_cleanKnots ha
  have hc1 := Finset.card_erase_add_one h1
  have hc0 := Finset.card_erase_add_one (Finset.mem_erase.mpr ⟨zero_ne_one,h0⟩ :
    (0:K)∈(cleanKnots A).erase 1)
  change S.card+1=((cleanKnots A).erase 1).card at hc0
  have hd : H.natDegree=4 := by
    change (nodalHull S).natDegree=4
    rw [natDegree_nodalHull]
    omega
  have hm4 : H.coeff 4=1 := hd ▸ (monic_nodalHull S).coeff_natDegree
  refine ⟨H.coeff 3+2,RKCert.Paired.beta_quartic_decoder H hd.le hm4 (fun k => ?_)⟩
  apply beta_probe_coeff ho H hd.le (by have:=k.isLt; omega)
  change probe A b k.val (evalNodes A ((X^2-X)*nodalHull S))=0
  rw [←RKCert.Paired.nodalHull_two_endpoint_factor (cleanKnots A) h0 h1]
  exact probe_zero_of_clean_roots hoff _ (fun _ => nodalHull_eval_of_mem) k.val

theorem order9_six_six_terminal_head {A : Matrix (Fin 12) (Fin 12) K} {b : (Fin 12→K)}
    (ha : ∀i j,i≤j → A i j=0) (ho : HasOrder A b 9)
    (hM : (cleanKnots A).card=6) (hN : (offKnots A).card=6)
    (P : K[X]) (hP : P.natDegree≤2)
    (fit : ∀ i, g A i≠0 → P.eval (nodes A i)=g A i)
    (off : ∀ x∈offKnots A, offMass A b x=0) :
    P.natDegree=2 ∧ P∣nodalHull (RKCert.Paired.endpointErase (cleanKnots A) 1) ∧
      g A (Fin.last 11)=0 ∧ nodes A (Fin.last 11)=1 ∧
      ∀ j, g A j=0 → nodes A j=1 → j=Fin.last 11 := by
  have hE5 := order9_grade_five_upper ha ho
  have h10 := gradeFiveState_rank (by omega : 6≤(cleanKnots A).card)
    (by omega : 4≤(offKnots A).card)
  have he : gradeFiveStateSpace A=treeSpace A 5 :=
    Submodule.eq_of_le_of_finrank_le (gradeFiveStateSpace_le A) (by omega)
  have hE : finrank K (treeSpace A 5)=10 := by rw [←he,h10]
  obtain ⟨hb,hc,hs,_⟩ := order9_rank_five_full_terminal ha ho hE
  let i := Fin.last 11
  have hs' : Pi.single i 1∈gradeFiveStateSpace A := by
    rw [he,←coordinate_as_single]; exact hs
  obtain ⟨z,hz⟩ := hs'
  rw [gradeFiveStateMap_eq_eval] at hz
  let Q := ofFn 6 z.1
  let R := ofFn 4 z.2
  change evalNodes A Q+diag (g A) (evalNodes A R)=Pi.single i 1 at hz
  have hi : g A i=0 := on_of_state_single (hz ▸ pairProfile_mem_onOffSpace fit Q R) hb off
  have hu : ∀ j, g A j=0 → nodes A j=1 → j=i :=
    fun j hj h => single_profile_on_unique hz hi hc j hj h
  let T := RKCert.Paired.endpointErase (cleanKnots A) 1
  have h1 : (1:K)∈cleanKnots A := mem_cleanKnots.mpr ⟨i,hi,hc⟩
  have hT : T.card=5 := by
    have := Finset.card_erase_add_one h1
    change T.card+1=(cleanKnots A).card at this
    omega
  have hQ : Q.natDegree≤5 := Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) _)
  have hR : R.natDegree≤3 := Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) _)
  have hq0 : ∀ x∈T, Q.eval x=0 := by
    intro x hx
    obtain ⟨hx1,hxOn⟩ := Finset.mem_erase.mp hx
    obtain ⟨j,hj,rfl⟩ := mem_cleanKnots.mp hxOn
    have hji : j≠i := fun e => hx1 (e.symm ▸ hc)
    simpa [hji] using profile_on_eval Q R hz hj
  have hq1 : Q.eval 1=1 := by
    have e := profile_on_eval Q R hz hi
    have hc' : nodes A i=1 := hc
    rw [hc'] at e
    simpa using e
  obtain ⟨a,hq⟩ := RKCert.Paired.polynomial_scalar_hull T Q (by omega) hq0
  have ha0 : a≠0 := by intro e; simp [hq,e] at hq1
  have qdeg : Q.natDegree=5 := by rw [hq,natDegree_C_mul ha0,natDegree_nodalHull,hT]
  have hz0 : Q+P*R=0 := eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _
    (offKnots A) (fun x hx => by
      obtain ⟨j,hj,rfl⟩ := mem_offKnots.mp hx
      have hji : j≠i := fun e => hj (e.symm ▸ hi)
      simpa [hji] using profile_off_eval hz fit hj)
    (by have := natDegree_add_le_of_degree_le hQ (natDegree_mul_le_of_le hP hR); omega)
  have hqp : Q=-(P*R) := by linear_combination hz0
  have hp2 : P.natDegree=2 := by
    by_contra! hne
    have hdeg := natDegree_mul_le_of_le (show P.natDegree≤1 by omega) hR
    rw [hqp,natDegree_neg] at qdeg
    omega
  refine ⟨hp2,⟨-(C a⁻¹*R),?_⟩,hi,hc,hu⟩
  calc
    nodalHull T=C a⁻¹*Q := by rw [hq,←mul_assoc,←map_mul,inv_mul_cancel₀ ha0,map_one,one_mul]
    _=P*-(C a⁻¹*R) := by rw [hqp]; ring

variable [LinearOrder K] [IsStrictOrderedRing K]

omit [CharZero K] in
theorem six_on_pencil_divisor_impossible {A : Matrix (Fin (s+1)) (Fin (s+1)) K}
    (ha : ∀i j,i≤j → A i j=0) (hF : zeroSpace A 4=band A 2)
    (hM : (cleanKnots A).card=6) (h1 : (1:K)∈cleanKnots A)
    (last : ∀ j, g A j=0 → nodes A j=1 → j=Fin.last s)
    (P : K[X]) (hPd : P.natDegree=2)
    (fit : ∀ j, g A j≠0 → P.eval (nodes A j)=g A j)
    (div : P∣nodalHull (RKCert.Paired.endpointErase (cleanKnots A) 1))
    {l : K} (pencil : nodalHull (RKCert.Paired.endpointErase (RKCert.Paired.endpointErase (cleanKnots A) 1) 0)=RKCert.Paired.lobattoPencil l) : False := by
  let _ : DecidableEq K := fun _ _ => Classical.propDecidable _
  let T := RKCert.Paired.endpointErase (cleanKnots A) 1
  let S := RKCert.Paired.endpointErase T 0
  have h0 : (0:K)∈T := Finset.mem_erase.mpr ⟨zero_ne_one,zero_mem_cleanKnots ha⟩
  have hTc : T.card+1=(cleanKnots A).card := Finset.card_erase_add_one h1
  have hSc : S.card+1=T.card := Finset.card_erase_add_one h0
  have cS : S.card=4 := by omega
  have hn : P≠0 := by intro h; simp [h] at hPd
  have hp0 := (first_nonzero_on_forces_head_shape ha hF hPd.le hn fit
    (exists_nonzero_on_of_card (by omega))).1
  have hDiv : P∣nodalHull S := by
    have cp : IsCoprime P (X:K[X]) := (irreducible_X.coprime_iff_not_dvd.mpr
      (fun h => hp0 ((coeff_zero_eq_eval_zero P).symm.trans (X_dvd_iff.mp h)))).symm
    rw [RKCert.Paired.nodalHull_erase_factor T h0,map_zero,sub_zero] at div
    exact cp.dvd_of_dvd_mul_left div
  obtain ⟨u,hu,hpu⟩ : ∃ u∈S, P.eval u≠0 := by
    by_contra! h
    exact hn (eq_zero_of_natDegree_lt_card_of_eval_eq_zero' P S h (by omega))
  let U : Set (Fin (s+1)) := {j | g A j=0 ∧ nodes A j∈S ∧ P.eval (nodes A j)≠0}
  have hU : U.Nonempty := by
    have hu' : u∈cleanKnots A := (Finset.mem_erase.mp (Finset.mem_erase.mp hu).2).2
    obtain ⟨j,hj,rfl⟩ := mem_cleanKnots.mp hu'
    exact ⟨j,hj,hu,hpu⟩
  obtain ⟨i,hi,hmin⟩ := wellFounded_lt.has_min U hU
  obtain ⟨hdi,hci,hpi⟩ := (show g A i=0 ∧ nodes A i∈S ∧ P.eval (nodes A i)≠0 from hi)
  let h := nodes A i
  change h∈S at hci
  have nh : h≠0 := (Finset.mem_erase.mp hci).1
  let W := RKCert.Paired.endpointErase S h
  have cW : W.card+1=S.card := Finset.card_erase_add_one hci
  obtain ⟨d,hd,hpd⟩ : ∃d∈W, P.eval d≠0 := by
    by_contra! e
    exact hn (eq_zero_of_natDegree_lt_card_of_eval_eq_zero' P W e (by omega))
  obtain ⟨hdh,hdS⟩ := Finset.mem_erase.mp hd
  obtain ⟨a,_,hfac⟩ := RKCert.Paired.quartic_divisor_two_complement_roots
    ((natDegree_nodalHull S).trans cS) hPd hDiv (nodalHull_eval_of_mem hci)
    (nodalHull_eval_of_mem hdS) hdh hpi hpd
  have tP : (primitive (X*P)).eval h=0 := by
    apply on_primitive_zero_of_prefix ha hF hdi (X*P)
      (natDegree_mul_le_of_le (by simp) (hPd.le)) (diag (nodes A) (g A))
      (clean_mixed_defect hF hdi)
    intro j hj
    by_cases qj : g A j=0
    · by_cases j0 : nodes A j=0
      · simp [qj,j0]
      · have j1 : nodes A j≠1 := fun e =>
          (ne_of_lt (hj.trans_le (Fin.le_last i))) (last j qj e)
        have js : nodes A j∈S := Finset.mem_erase.mpr ⟨j0,
          Finset.mem_erase.mpr ⟨j1,mem_cleanKnots.mpr ⟨j,qj,rfl⟩⟩⟩
        have e : P.eval (nodes A j)=0 := by by_contra hn'; exact hmin j ⟨qj,js,hn'⟩ hj
        simp [qj,e]
    · simp [fit j qj]
  exact RKCert.Paired.lobattoPencil_complement_primitive_ne_zero hPd.le nh hdh
    (pencil.symm.trans hfac) ((scalar_primitive (X*P)).symm ▸ tP)

omit [CharZero K] in
theorem order9_no_six_off_six_on {A : Matrix (Fin 12) (Fin 12) K} {b : (Fin 12→K)}
    (ha : ∀i j,i≤j → A i j=0) (ho : HasOrder A b 9)
    (N : (offKnots A).card=6) :
    (cleanKnots A).card≠6 := by
  intro M
  obtain ⟨_,h3,h4,_⟩ := order9_forward_chart ha ho (by decide)
  obtain ⟨P,dP,_,_,hF,fit⟩ := two_curve_head h3 h4 (by omega)
  have hoff : ∀ x∈offKnots A, offMass A b x=0 :=
    fun x hx => offMass_zero_of_head ho fit (by omega) x hx
  obtain ⟨dP',hdiv,hi,hc,huniq⟩ := order9_six_six_terminal_head ha ho M N P dP fit hoff
  have h1 : (1:K)∈cleanKnots A := mem_cleanKnots.mpr ⟨Fin.last 11,hi,hc⟩
  obtain ⟨l,hl⟩ := order9_six_on_pencil ha ho M h1 hoff
  exact six_on_pencil_divisor_impossible ha hF M h1 huniq P dP' fit hdiv hl

omit [CharZero K] in
/-- Every physical ordered twelve-stage ERK9 tableau must have exactly five
defective knots. The clean count is five or six; the five-off/five-clean
exclusion and the actual six-clean atlas interface remain separate. -/
theorem order9_exactly_five_off {A : Matrix (Fin 12) (Fin 12) K} {b : Fin 12→K}
    (ha : ∀i j,i≤j → A i j=0) (ho : HasOrder A b 9) :
    (offKnots A).card=5 ∧ ((cleanKnots A).card=5 ∨ (cleanKnots A).card=6) := by
  obtain ⟨lo,hi,cl,cu,_,_⟩ := order9_middle_census ha ho
  have no7 := order9_no_seven_off ha ho
  have no6 : (offKnots A).card≠6 := by
    intro eq
    have n6 := order9_no_six_off_six_on ha ho eq
    exact order9_no_five_clean_six_or_seven ha ho (by omega) (Or.inl eq)
  exact ⟨by omega,by omega⟩

omit [CharZero K] in
theorem explicit_order_nine_off_count_ne_five_at_least_thirteen {n : ℕ}
    {A : Matrix (Fin n) (Fin n) K} {b : Fin n→K}
    (ha : ∀i j,i≤j → A i j=0) (ho : HasOrder A b 9) (off : (offKnots A).card≠5) : 13≤n := by
  by_contra! low
  have size := (order9_forward_chart ha ho (by omega)).1
  subst n
  exact off (order9_exactly_five_off ha ho).1
end RKResearch.Certified.Graded.MultiOff
