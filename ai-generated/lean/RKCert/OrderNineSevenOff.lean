module
public import RKCert.SevenOffInterpolation

@[expose] public section
namespace RKCert.FixedFactor
open Polynomial Module RKCert.Paired RKCert.Endpoint
open scoped Classical
variable {K : Type*} [Field K] {s:ℕ}

noncomputable def pairEleven (A : Fin s→Fin s→K) : ((Fin 5→K)×(Fin 6→K)) →ₗ[K] Vec K s :=
  (polyEval A 4).coprod ((diag (qdef A)).comp (polyEval A 5))

theorem pairEleven_apply (A : Fin s→Fin s→K) (v : (Fin 5→K)×(Fin 6→K)) :
    pairEleven A v=evalNodes A (ofFn 5 v.1)+diag (qdef A) (evalNodes A (ofFn 6 v.2)) := by
  rw [evalNodes_ofFn A 4,evalNodes_ofFn A 5]
  rfl

theorem pairEleven_injective {A : Fin s→Fin s→K} (M : 5≤(onNodes A).card)
    (N : 6≤(supportedNodes A (qdef A)).card) : Function.Injective (pairEleven A) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  let V:=ofFn 5 z.1
  let W:=ofFn 6 z.2
  have dV : V.natDegree<5:=ofFn_natDegree_lt (by decide) _
  have dW : W.natDegree<6:=ofFn_natDegree_lt (by decide) _
  have atAll (i : Fin s) : V.eval (nodes A i)+qdef A i*W.eval (nodes A i)=0 := by
    rw [pairEleven_apply] at hz
    exact congrFun hz i
  have v0 : V=0 := eq_zero_of_natDegree_lt_card_of_eval_eq_zero' V (onNodes A)
    (fun x hx=>by obtain ⟨i,hi,rfl⟩:=mem_onNodes.mp hx; simpa [hi] using atAll i) (by omega)
  have w0 : W=0:=eq_zero_of_natDegree_lt_card_of_eval_eq_zero' W (supportedNodes A (qdef A))
    (fun x hx=>by obtain ⟨i,hi,rfl⟩:=mem_supportedNodes.mp hx
                  exact (mul_eq_zero.mp (by simpa [v0] using atAll i)).resolve_left hi) (by omega)
  exact Prod.ext (injective_ofFn 5 (v0.trans (ofFn_zero _).symm))
    (injective_ofFn 6 (w0.trans (ofFn_zero _).symm))

variable [CharZero K]

theorem pairEleven_range_le (A : Fin s→Fin s→K) : LinearMap.range (pairEleven A)≤treeSpace A 7 := by
  rintro _ ⟨v,rfl⟩
  rw [pairEleven_apply]
  apply (treeSpace A 7).add_mem (evalNodes_mem_treeSpace _ _ (by have:=ofFn_natDegree_lt (by decide : 0<5) v.1;omega))
  apply zeroSpace_le_treeSpace A 7
  apply chainSpan_le_zeroSpace (qdef_mem A) 5
  exact chainSpan_iff_polynomial.mpr ⟨_,Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) _),rfl⟩

omit [CharZero K] in
theorem off_poly_of_range {A : Fin s→Fin s→K} (M:5≤(onNodes A).card)
    (P F : K[X]) (fit : ∀i,qdef A i≠0→P.eval (nodes A i)=qdef A i)
    (onF : ∀x∈onNodes A,F.eval x=0)
    (range : evalNodes A F∈LinearMap.range (pairEleven A)) :
    ∃ T:K[X], T.natDegree≤5 ∧ ∀x∈supportedNodes A (qdef A), F.eval x=P.eval x*T.eval x := by
  obtain ⟨v,hv⟩:=range
  rw [pairEleven_apply] at hv
  let V:=ofFn 5 v.1
  let T:=ofFn 6 v.2
  have he (i : Fin s) : V.eval (nodes A i)+qdef A i*T.eval (nodes A i)=F.eval (nodes A i) :=
    congrFun hv i
  have v0 : V=0 := eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ (onNodes A) (fun x hx=>by
    obtain ⟨i,hi,rfl⟩:=mem_onNodes.mp hx
    simpa [hi,onF _ hx] using he i) (by
      have dV : V.natDegree<5:=ofFn_natDegree_lt (by decide) _
      omega)
  refine ⟨T,Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) _),?_⟩
  intro x hx
  obtain ⟨i,hi,rfl⟩:=mem_supportedNodes.mp hx
  simpa [v0,fit i hi] using (he i).symm

/-- For any two-curve physical stage space, five on and seven off sites
already require a full 12-dimensional seventh-grade stage span when the
fitted quadratic-or-lower head does not divide the on-node hull. -/
theorem seven_off_rank {A : Fin s→Fin s→K} (M:(onNodes A).card=5)
    (N:(supportedNodes A (qdef A)).card=7) (P : K[X]) (dP:P.natDegree≤2)
    (fit : ∀i,qdef A i≠0→P.eval (nodes A i)=qdef A i)
    (nondiv : ¬P∣nodalHull (onNodes A)) : 12≤finrank K (treeSpace A 7) := by
  let : Infinite K := Infinite.of_injective (fun n : ℕ => (n:K)) Nat.cast_injective
  let Q:=nodalHull (onNodes A)
  have dQ : Q.natDegree=5 := (natDegree_nodalHull _).trans M
  have h11 : finrank K (LinearMap.range (pairEleven A))=11 := by
    rw [LinearMap.finrank_range_of_inj (pairEleven_injective (by omega : 5≤(onNodes A).card)
        (by omega : 6≤(supportedNodes A (qdef A)).card)),Module.finrank_prod,
        Module.finrank_fin_fun,Module.finrank_fin_fun]
  by_contra! small
  have e:=Submodule.eq_of_le_of_finrank_le (pairEleven_range_le A) (by omega)
  have mh (F:K[X]) (f:F.natDegree≤7) : evalNodes A F∈LinearMap.range (pairEleven A) :=
    e ▸ evalNodes_mem_treeSpace A F f
  obtain ⟨T,dT,atQ⟩:=off_poly_of_range (by omega : 5≤(onNodes A).card) P Q fit
    (fun _ h=>nodalHull_eval_of_mem h) (mh Q (by omega))
  have dX : (X*Q).natDegree≤6 := natDegree_mul_le_of_le (by simp) dQ.le
  obtain ⟨U,dU,atXQ⟩:=off_poly_of_range (by omega : 5≤(onNodes A).card) P (X*Q) fit
    (fun _ h=>by rw [eval_mul,show Q.eval _=0 from nodalHull_eval_of_mem h,mul_zero]) (mh _ (by omega))
  exact seven_off_pair_obstruction _ N P Q dP dQ.le nondiv (fun _ hx=>by
    obtain ⟨i,hi,rfl⟩:=mem_supportedNodes.mp hx; rwa [fit i hi]) T U dT dU atQ atXQ

/-- A genuine strict order-nine twelve-stage tableau never has exactly seven
distinct quadratic-defect abscissas. No ordering or distinct-row hypothesis. -/
theorem order9_no_seven_off {A : Fin 12→Fin 12→K} {b : Vec K 12}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 9) :
    (supportedNodes A (qdef A)).card≠7 := by
  intro N
  obtain ⟨hb,h3,h4,_,_,_,_,_⟩:=order9_twelve_stage_chart ha ho
  obtain ⟨P,dP,_,_,hF,fit⟩:=two_curve_head h3 h4 (by omega)
  have hoff : ∀ x∈supportedNodes A (qdef A), offWeight A b x=0 :=
    fun x hx=>offWeight_eq_zero_from_head ho P fit (by omega) x hx
  have low:=five_on_of_aggregate_zero (s:=11) ha ho (by decide) hoff
  have budget:=on_off_card_le A
  have M : (onNodes A).card=5 := by omega
  have nd:=order9_five_on_head_not_dvd (s:=11) ha ho M hoff hF P dP fit
  have h7:=seven_off_rank M N P dP fit nd
  have bk:=backward_count ha ho 7 0 (by decide)
  have hz : backSeed1 A b=0 := by
    by_contra h
    have h1 : finrank K (back A b 0)=1 := finrank_span_singleton h
    omega
  have sup (i:Fin 12) (h : Fin.last 11 < i) : b i=0 := by
    have hi:=i.isLt
    change 11 < i.val at h
    omega
  have hc : nodes A (Fin.last 11)=1 := (sub_eq_zero.mp (last_mirror_zero ha hb sup hz)).symm
  have hd:=onOffSpace_rank A
  have top : onOffSpace A=⊤:=Submodule.eq_top_of_finrank_eq (by
    rw [hd,M,N,Module.finrank_fin_fun])
  have isOn:=on_of_state_single (i:=Fin.last 11) (by rw [top]; trivial) hb hoff
  exact one_not_on_of_five (s:=11) ha ho M hoff (mem_onNodes.mpr ⟨Fin.last 11,isOn,hc⟩)

end RKCert.FixedFactor
