module

public import RKCert.ERKOrderNinePencil
public import RKCert.ERKOrderNineStateSupport

@[expose] public section

/-! # Physical exclusion of the six-off / six-on order-nine chart

At grade five, the exact two-curve span has rank ten. Its terminal
singleton forces a polynomial identity on all six off nodes and a
quadratic divisibility on the five nonterminal on nodes. The earliest
eligible physical row is then excluded by the exact pencil test.
-/
namespace RKCert.Paired
open Module Polynomial RKCert.Endpoint
open scoped Classical

variable {K : Type*} [Field K] [CharZero K] {s : ℕ}

/-- The numerical census, exact pair rank and terminal singleton have
stronger consequences than the rank-six interpolation count alone. -/
theorem order9_six_six_terminal_head {A : Fin 12 → Fin 12 → K} {b : Vec K 12}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 9)
    (hM : (onNodes A).card=6) (hN : (supportedNodes A (qdef A)).card=6)
    (P : K[X]) (hP : P.natDegree≤2)
    (fit : ∀ i, qdef A i≠0 → P.eval (nodes A i)=qdef A i)
    (off : ∀ x∈supportedNodes A (qdef A), offWeight A b x=0) :
    P.natDegree=2 ∧ P∣nodalHull (endpointErase (onNodes A) 1) ∧
      qdef A (Fin.last 11)=0 ∧ nodes A (Fin.last 11)=1 ∧
      ∀ j, qdef A j=0 → nodes A j=1 → j=Fin.last 11 := by
  obtain ⟨hb,_,_,_,_,_,hE5,_⟩ := order9_twelve_stage_chart ha ho
  have h10 := gradeFiveState_rank (by omega : 6≤(onNodes A).card)
    (by omega : 4≤(supportedNodes A (qdef A)).card)
  have he : gradeFiveStateSpace A=treeSpace A 5 :=
    Submodule.eq_of_le_of_finrank_le (gradeFiveStateSpace_le A) (by omega)
  have hE : finrank K (treeSpace A 5)=10 := by rw [←he,h10]
  obtain ⟨_,hc,hs,_,_,_⟩ := order9_rank_five_full ha ho hE
  let i := Fin.last 11
  have hs' : Pi.single i 1∈gradeFiveStateSpace A := he ▸ hs
  obtain ⟨z,hz⟩ := hs'
  rw [gradeFiveStateMap_eq_eval] at hz
  let Q := ofFn 6 z.1
  let R := ofFn 4 z.2
  change evalNodes A Q+diag (qdef A) (evalNodes A R)=Pi.single i 1 at hz
  have hi : qdef A i=0 := on_of_state_single (hz ▸ pairProfile_mem_onOffSpace fit Q R) hb off
  have hu : ∀ j, qdef A j=0 → nodes A j=1 → j=i :=
    fun j hj h => single_profile_on_unique hz hi hc j hj h
  let T := endpointErase (onNodes A) 1
  have h1 : (1:K)∈onNodes A := mem_onNodes.mpr ⟨i,hi,hc⟩
  have hT : T.card=5 := by
    have := Finset.card_erase_add_one h1
    change T.card+1=(onNodes A).card at this
    omega
  have hQ : Q.natDegree≤5 := Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) _)
  have hR : R.natDegree≤3 := Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) _)
  have hq0 : ∀ x∈T, Q.eval x=0 := by
    intro x hx
    obtain ⟨hx1,hxOn⟩ := Finset.mem_erase.mp hx
    obtain ⟨j,hj,rfl⟩ := mem_onNodes.mp hxOn
    have hji : j≠i := fun e => hx1 (e.symm ▸ hc)
    simpa [hji] using profile_on_eval Q R hz hj
  have hq1 : Q.eval 1=1 := by
    have e := profile_on_eval Q R hz hi
    have hc' : nodes A i=1 := hc
    rw [hc'] at e
    simpa using e
  obtain ⟨a,hq⟩ := polynomial_scalar_hull T Q (by omega) hq0
  have ha0 : a≠0 := by intro e; simp [hq,e] at hq1
  have qdeg : Q.natDegree=5 := by rw [hq,natDegree_C_mul ha0,natDegree_nodalHull,hT]
  have hz0 : Q+P*R=0 := eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _
    (supportedNodes A (qdef A)) (fun x hx => by
      obtain ⟨j,hj,rfl⟩ := mem_supportedNodes.mp hx
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

section Ordered
variable [LinearOrder K] [IsStrictOrderedRing K]

omit [CharZero K] in
theorem six_on_pencil_divisor_impossible {A : Fin (s+1) → Fin (s+1) → K}
    (ha : StrictLower A) (hF : zeroSpace A 4=chainSpan A (qdef A) 2)
    (hM : (onNodes A).card=6) (h1 : (1:K)∈onNodes A)
    (last : ∀ j, qdef A j=0 → nodes A j=1 → j=Fin.last s)
    (P : K[X]) (hPd : P.natDegree=2)
    (fit : ∀ j, qdef A j≠0 → P.eval (nodes A j)=qdef A j)
    (div : P∣nodalHull (endpointErase (onNodes A) 1))
    {l : K} (pencil : nodalHull (endpointErase (endpointErase (onNodes A) 1) 0)=lobattoPencil l) : False := by
  let _ : DecidableEq K := fun _ _ => Classical.propDecidable _
  let T := endpointErase (onNodes A) 1
  let S := endpointErase T 0
  have h0 : (0:K)∈T := Finset.mem_erase.mpr ⟨zero_ne_one,zero_mem_onNodes ha⟩
  have hTc : T.card+1=(onNodes A).card := Finset.card_erase_add_one h1
  have hSc : S.card+1=T.card := Finset.card_erase_add_one h0
  have cS : S.card=4 := by omega
  have hn : P≠0 := by intro h; simp [h] at hPd
  have hp0 := (first_nonzero_on_forces_head_shape ha hF hPd.le hn fit
    (exists_nonzero_on_of_card (by omega))).1
  have hDiv : P∣nodalHull S := by
    have cp : IsCoprime P (X:K[X]) := (irreducible_X.coprime_iff_not_dvd.mpr
      (fun h => hp0 ((coeff_zero_eq_eval_zero P).symm.trans (X_dvd_iff.mp h)))).symm
    rw [nodalHull_erase_factor T h0,map_zero,sub_zero] at div
    exact cp.dvd_of_dvd_mul_left div
  obtain ⟨u,hu,hpu⟩ : ∃ u∈S, P.eval u≠0 := by
    by_contra! h
    exact hn (eq_zero_of_natDegree_lt_card_of_eval_eq_zero' P S h (by omega))
  let U : Set (Fin (s+1)) := {j | qdef A j=0 ∧ nodes A j∈S ∧ P.eval (nodes A j)≠0}
  have hU : U.Nonempty := by
    have hu' : u∈onNodes A := (Finset.mem_erase.mp (Finset.mem_erase.mp hu).2).2
    obtain ⟨j,hj,rfl⟩ := mem_onNodes.mp hu'
    exact ⟨j,hj,hu,hpu⟩
  obtain ⟨i,hi,hmin⟩ := wellFounded_lt.has_min U hU
  obtain ⟨hdi,hci,hpi⟩ := (show qdef A i=0 ∧ nodes A i∈S ∧ P.eval (nodes A i)≠0 from hi)
  let h := nodes A i
  change h∈S at hci
  have nh : h≠0 := (Finset.mem_erase.mp hci).1
  let W := endpointErase S h
  have cW : W.card+1=S.card := Finset.card_erase_add_one hci
  obtain ⟨d,hd,hpd⟩ : ∃d∈W, P.eval d≠0 := by
    by_contra! e
    exact hn (eq_zero_of_natDegree_lt_card_of_eval_eq_zero' P W e (by omega))
  obtain ⟨hdh,hdS⟩ := Finset.mem_erase.mp hd
  obtain ⟨a,_,hfac⟩ := quartic_divisor_two_complement_roots
    ((natDegree_nodalHull S).trans cS) hPd hDiv (nodalHull_eval_of_mem hci)
    (nodalHull_eval_of_mem hdS) hdh hpi hpd
  have tP : (primitive (X*P)).eval h=0 := by
    apply on_primitive_zero_of_prefix ha hF hdi (X*P)
      (natDegree_mul_le_of_le (by simp) (hPd.le)) (diag (nodes A) (qdef A))
      (on_row_quartic_conditions hF hdi).2.2
    intro j hj
    by_cases qj : qdef A j=0
    · by_cases j0 : nodes A j=0
      · simp [qj,j0]
      · have j1 : nodes A j≠1 := fun e =>
          (ne_of_lt (hj.trans_le (Fin.le_last i))) (last j qj e)
        have js : nodes A j∈S := Finset.mem_erase.mpr ⟨j0,
          Finset.mem_erase.mpr ⟨j1,mem_onNodes.mpr ⟨j,qj,rfl⟩⟩⟩
        have e : P.eval (nodes A j)=0 := by by_contra hn'; exact hmin j ⟨qj,js,hn'⟩ hj
        simp [qj,e]
    · simp [fit j qj]
  exact lobattoPencil_complement_primitive_ne_zero hPd.le nh hdh
    (pencil.symm.trans hfac) tP

omit [CharZero K] in
/-- The actual order-nine twelve-stage chart cannot have precisely six
defective and six clean state abscissas over an ordered field. -/
theorem order9_no_six_off_six_on {A : Fin 12 → Fin 12 → K} {b : Vec K 12}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 9)
    (N : (supportedNodes A (qdef A)).card=6) :
    (onNodes A).card≠6 := by
  intro M
  obtain ⟨_,h3,h4,_,_,_,_,_⟩ := order9_twelve_stage_chart ha ho
  obtain ⟨P,dP,_,_,hF,fit⟩ := two_curve_head h3 h4 (by omega)
  have hoff : ∀ x∈supportedNodes A (qdef A), offWeight A b x=0 :=
    fun x hx => offWeight_eq_zero_from_head ho P fit (by omega) x hx
  obtain ⟨dP',hdiv,hi,hc,huniq⟩ := order9_six_six_terminal_head ha ho M N P dP fit hoff
  have h1 : (1:K)∈onNodes A := mem_onNodes.mpr ⟨Fin.last 11,hi,hc⟩
  obtain ⟨l,hl⟩ := order9_six_on_pencil ha ho M h1 hoff
  exact six_on_pencil_divisor_impossible ha hF M h1 huniq P dP' fit hdiv hl

end Ordered
end RKCert.Paired
