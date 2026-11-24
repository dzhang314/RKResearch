module

public import RKCert.ERKOrderNineFiveSixK8Actual
public import RKCert.ERKOrderNineFiveSixCollisionPoly
public import RKCert.ERKLowPseudoRemainder

@[expose] public section

/-! # Complete physical terminal interface for the five-off/six-on chart

Only the outside-tableau modular norm exclusion remains after this
theorem. No hypothesis is made about whether either affine equation
coefficient vanishes.
-/
namespace RKCert.Paired
open Polynomial RKCert.Endpoint
open scoped Classical
variable {K : Type*} [Field K]

noncomputable def sixOnP0 (h : K) : K[X] := C (3*h^2)-C 6*X^2

noncomputable def sixOnP1 (h : K) : K[X] := C (3*h)*X-C 4*X^2

theorem sixOnP0_eval (h x : K) : (sixOnP0 h).eval x=fixedRadauP0 h x := by simp [sixOnP0,fixedRadauP0]

theorem sixOnP1_eval (h x : K) : (sixOnP1 h).eval x=fixedRadauP1 h x := by simp [sixOnP1,fixedRadauP1,mul_assoc]

noncomputable def sixOnHat (h u v : K) : K[X] :=
  C (sixOnF u v (fixedRadauP1 h))*sixOnP0 h - C (sixOnF u v (fixedRadauP0 h))*sixOnP1 h

noncomputable def sixOnPort (u v : K) : K[X] :=
  C (3*(u-v))*X-C (4*u^2-5*u*v+2*v-1)

noncomputable def sixOnO5 (h u v l : K) : K :=
  quadraticPremDet (sixOnHat h u v) (sixOnPort u v*(X^2*(X-C h)^2)) (X*lobattoPencil l)

noncomputable def sixOnO6 (h u v l : K) : K :=
  quadraticPremDet (sixOnHat h u v) (sixOnPort u v*primitive (X*sixOnHat h u v))
    (X*lobattoPencil l)

noncomputable def sixOnTerminalProduct (h u v l : K) : K :=
  (sixOnHat h u v).coeff 2*sixOnO5 h u v l*sixOnO6 h u v l*sixOnHc h u v

theorem sixOnP0_degree (h : K) : (sixOnP0 h).natDegree≤2 := by
  unfold sixOnP0
  have a : (C (3*h^2)).natDegree≤2 := by simp only [natDegree_C,Nat.zero_le]
  exact natDegree_sub_le_of_le a ((natDegree_C_mul_le _ _).trans (natDegree_X_pow_le _))

theorem sixOnP1_degree (h : K) : (sixOnP1 h).natDegree≤2 := by
  unfold sixOnP1
  have a : (X:K[X]).natDegree≤2 := by simp
  exact natDegree_sub_le_of_le ((natDegree_C_mul_le _ _).trans a)
    ((natDegree_C_mul_le _ _).trans (natDegree_X_pow_le _))

theorem sixOnHat_degree (h u v : K) : (sixOnHat h u v).natDegree≤2 :=
  natDegree_sub_le_of_le ((natDegree_C_mul_le _ _).trans (sixOnP0_degree _))
    ((natDegree_C_mul_le _ _).trans (sixOnP1_degree _))

theorem sixOnPort_degree (u v : K) : (sixOnPort u v).natDegree≤1 := by
  unfold sixOnPort
  have a : (X:K[X]).natDegree≤1 := by simp
  have b : (C (4*u^2-5*u*v+2*v-1)).natDegree≤1 := by simp only [natDegree_C,Nat.zero_le]
  exact natDegree_sub_le_of_le ((natDegree_C_mul_le _ _).trans a) b

section Ordered
variable [LinearOrder K] [IsStrictOrderedRing K]

theorem ActualSixOnFG.prefix_on_hull
    {A : Fin 12→Fin 12→K} {b : Vec K 12}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 9)
    (N : (supportedNodes A (qdef A)).card=5) (M : (onNodes A).card=6)
    {P : K[X]} (fit : ∀i,qdef A i≠0 → P.eval (nodes A i)=qdef A i)
    (fg : ActualSixOnFG A P) :
    nodalHull (endpointErase (onNodes A) 1)=X*lobattoPencil fg.pencil_parameter := by
  let _ : DecidableEq K := fun _ _ => Classical.propDecidable _
  obtain ⟨_,_,_,hc,he,_,last⟩ := order9_five_six_stage_chart ha ho N M fit
  let T := endpointErase (onNodes A) 1
  let S := endpointErase T 0
  have one : (1:K)∈onNodes A := mem_onNodes.mpr ⟨_,hc,he⟩
  have zero : (0:K)∈T := Finset.mem_erase.mpr ⟨zero_ne_one,zero_mem_onNodes ha⟩
  have Ts : T.card+1=(onNodes A).card := Finset.card_erase_add_one one
  have Ss : S.card+1=T.card := Finset.card_erase_add_one zero
  have cS : S.card=4 := by omega
  let W : Fin 4→K := ![nodes A (lowPrefix10 fg.first),nodes A (lowPrefix10 fg.middle),
    nodes A (lowPrefix10 (8:Fin 10)),nodes A (lowPrefix10 (Fin.last 9))]
  let U := Finset.univ.image W
  have cU : U.card=4 := by
    simp only [U,Finset.card_image_of_injective _ (show Function.Injective W from fg.root_set_injective),
      Finset.card_univ,Fintype.card_fin]
  have mem (i : Fin 10) (gi : qdef A (lowPrefix10 i)=0) (z : nodes A (lowPrefix10 i)≠0) :
      nodes A (lowPrefix10 i)∈S :=
    Finset.mem_erase.mpr ⟨z,Finset.mem_erase.mpr ⟨first_prefix_clean_value_ne_one last i gi,
      mem_onNodes.mpr ⟨_,gi,rfl⟩⟩⟩
  have su : U⊆S := by
    intro x hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    fin_cases i
    · exact mem _ fg.first_clean fg.first_nonzero
    · exact mem _ fg.middle_clean fg.middle_nonzero
    · exact mem _ fg.late_u_clean fg.late_u_nonzero
    · exact mem _ fg.late_v_clean fg.late_v_nonzero
  have eU : U=S := Finset.eq_of_subset_of_card_le su (by omega)
  let Q := lobattoPencil fg.pencil_parameter
  obtain ⟨t,e⟩ := polynomial_scalar_hull S Q
    (by change (lobattoPencil fg.pencil_parameter).natDegree≤S.card; rw [lobattoPencil_natDegree,cS]) (by
      intro x hx
      rw [←eU] at hx
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
      exact fg.pencil_roots i)
  have hC : (nodalHull S : K[X]).coeff 4=1 := by
    rw [←(natDegree_nodalHull (K:=K) S).trans cS]
    exact (monic_nodalHull S).coeff_natDegree
  have t1 : t=1 := by
    have a := congrArg (fun P : K[X]=>P.coeff 4) e
    simpa [Q,lobattoPencil,coeff_monomial,coeff_C_mul,hC] using a.symm
  have f : Q=nodalHull S := by simpa [t1] using e
  change nodalHull T=X*Q
  rw [nodalHull_erase_factor T zero,map_zero,sub_zero,f]

theorem ActualSixOnFG.hat_scale {A : Fin 12→Fin 12→K} {P : K[X]} (fg : ActualSixOnFG A P) :
    let h := nodes A (lowPrefix10 fg.first)
    let u := nodes A (lowPrefix10 (8:Fin 10))
    let v := nodes A (lowPrefix10 (Fin.last 9))
    let H := sixOnHat h u v
    H.coeff 2≠0 → ∃ a : K,a≠0 ∧ H=C a*P ∧ H.natDegree=2 ∧ P.natDegree=2 := by
  dsimp only
  intro n
  let h := nodes A (lowPrefix10 fg.first)
  let u := nodes A (lowPrefix10 (8:Fin 10))
  let v := nodes A (lowPrefix10 (Fin.last 9))
  let H := sixOnHat h u v
  let f₀ := sixOnF u v (fixedRadauP0 h)
  let f₁ := sixOnF u v (fixedRadauP1 h)
  let t := fg.affine_parameter
  let a := fg.head_scale
  have z : f₀+t*f₁=0 := by
    have z := fg.F_zero
    change sixOnF u v (fun x=>fixedRadauP0 h x+t*fixedRadauP1 h x)=0 at z
    dsimp only [f₀,f₁]
    unfold sixOnF at z ⊢
    linear_combination z
  have e : f₀= -t*f₁ := by linear_combination z
  have fn : f₁≠0 := by
    intro e1
    have e0 : f₀=0 := by simp [e,e1]
    have hZ : H=0 := by
      change C f₁*sixOnP0 h-C f₀*sixOnP1 h=0
      rw [e0,e1,map_zero,zero_mul,zero_mul,sub_self]
    exact n (by change H.coeff 2=0; simp [hZ])
  have da : f₁/a≠0 := div_ne_zero fn fg.head_scale_nonzero
  have er : H=C (f₁/a)*P := by
    let _ : Infinite K := Infinite.of_injective (fun n : ℕ => (n:K)) Nat.cast_injective
    apply Polynomial.funext
    intro x
    change (C f₁*sixOnP0 h-C f₀*sixOnP1 h).eval x=(C (f₁/a)*P).eval x
    rw [eval_sub,eval_mul,eval_mul,eval_mul,eval_C,eval_C,eval_C,
      sixOnP0_eval,sixOnP1_eval,fg.head_shape,e]
    have ka : f₁/a*a=f₁ := div_mul_cancel₀ _ fg.head_scale_nonzero
    change _=f₁/a*(a*(fixedRadauP0 h x+t*fixedRadauP1 h x))
    rw [←mul_assoc,ka]
    ring
  have dH : H.natDegree=2 := natDegree_eq_of_le_of_coeff_ne_zero (sixOnHat_degree _ _ _) n
  have dP : P.natDegree=2 := by
    have d := dH
    rw [er,natDegree_C_mul da] at d
    exact d
  exact ⟨f₁/a,da,er,dH,dP⟩

set_option maxHeartbeats 1200000 in
/-- Terminal product zero is forced by an actual (5,6) tableau,
including the linear and all three physical stage-placement cases. -/
theorem ActualSixOnFG.terminal_product_zero
    {A : Fin 12→Fin 12→K} {b : Vec K 12}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 9)
    (N : (supportedNodes A (qdef A)).card=5) (M : (onNodes A).card=6)
    (hF : zeroSpace A 4=chainSpan A (qdef A) 2)
    {P : K[X]} (dP : P.natDegree≤2) (pn : P≠0)
    (fit : ∀i,qdef A i≠0 → P.eval (nodes A i)=qdef A i)
    (fg : ActualSixOnFG A P) :
    sixOnTerminalProduct (nodes A (lowPrefix10 fg.first)) (nodes A (lowPrefix10 (8:Fin 10)))
      (nodes A (lowPrefix10 (Fin.last 9))) fg.pencil_parameter=0 := by
  let h := nodes A (lowPrefix10 fg.first)
  let u := nodes A (lowPrefix10 (8:Fin 10))
  let v := nodes A (lowPrefix10 (Fin.last 9))
  let l := fg.pencil_parameter
  let H := sixOnHat h u v
  let Q := X*lobattoPencil l
  change H.coeff 2*sixOnO5 h u v l*sixOnO6 h u v l*sixOnHc h u v=0
  by_cases zero : H.coeff 2=0
  · rw [zero,zero_mul,zero_mul,zero_mul]
  by_cases on : qdef A (lowPrefix10 (7:Fin 10))=0
  · rw [show sixOnHc h u v=0 from order9_actual_five_six_on_eighth_atlas ha ho N M hF dP fit fg on,
      mul_zero]
  obtain ⟨a,an,er,dH,dP'⟩ := fg.hat_scale zero
  change H=C a*P at er
  have q : nodalHull (endpointErase (onNodes A) 1)=Q := fg.prefix_on_hull ha ho N M fit
  have dQ : Q.natDegree≤5 := by
    have z := natDegree_mul_le_of_le (show (X:K[X]).natDegree≤1 by simp) (lobattoPencil_natDegree l).le
    exact z
  have dH' : H.natDegree≤2 := dH.le
  have div : H∣P := ⟨C a⁻¹,by
    rw [er]
    calc P=C (a*a⁻¹)*P := by rw [mul_inv_cancel₀ an,map_one,one_mul]
      _=(C a*P)*C a⁻¹ := by rw [map_mul]; ring⟩
  obtain ⟨_,_,place⟩ := order9_actual_five_six_off_eighth ha ho N M hF dP' pn fit fg on
  rcases place with ⟨_,t,_,z⟩|⟨_,t,_,z⟩
  · let U := sixOnPort u v*(X^2*(X-C h)^2)
    have dU : U.natDegree≤5 := by
      have a1 : (X^2:K[X]).natDegree≤2 := natDegree_X_pow_le _
      have a2 : ((X-C h)^2).natDegree≤2 := natDegree_pow_le_of_le _ (show (X-C h).natDegree≤1 by simp)
      exact natDegree_mul_le_of_le (sixOnPort_degree _ _) (natDegree_mul_le_of_le a1 a2)
    rw [q] at z
    have e := quadraticPremDet_zero_of_dvd dH dU dQ (div.trans z)
    change sixOnO5 h u v l=0 at e
    rw [e,mul_zero,zero_mul,zero_mul]
  · let D := sixOnPort u v
    let U := D*primitive (X*H)
    have dU : U.natDegree≤5 := by
      have e : (X*H).natDegree≤3 := natDegree_mul_le_of_le (by simp) dH'
      exact natDegree_mul_le_of_le (sixOnPort_degree _ _) (primitive_natDegree_le e)
    have es : U=C a*(D*primitive (X*P)) := by
      change D*primitive (X*H)=_
      rw [er]
      have ex : X*(C a*P)=C a*(X*P) := by ring
      rw [ex,←smul_eq_C_mul,map_smul,smul_eq_C_mul]
      ring
    have ep : C (t/a)*U=C t*(D*primitive (X*P)) := by
      rw [es,←mul_assoc,←map_mul,div_mul_cancel₀ _ an]
    rw [q] at z
    change P∣Q-C t*(D*primitive (X*P)) at z
    rw [←ep] at z
    have e := quadraticPremDet_zero_of_dvd dH dU dQ (div.trans z)
    change sixOnO6 h u v l=0 at e
    rw [e,mul_zero,zero_mul]

/-- Complete physical interface for the remaining two-curve atlas.
The separate scalar norm/gcd exclusion is not asserted here. -/
theorem order9_actual_five_six_atlas_input
    {A : Fin 12→Fin 12→K} {b : Vec K 12}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 9)
    (N : (supportedNodes A (qdef A)).card=5) (M : (onNodes A).card=6) :
    ∃ h u v l : K,
      let W : Fin 4→K := ![h,2-l-h-u-v,u,v]
      Function.Injective W ∧ (∀i,(lobattoPencil l).eval (W i)=0) ∧
        sixOnK8 h u v l=0 ∧ sixOnTerminalProduct h u v l=0 := by
  obtain ⟨_,h3,h4,_,_,_,_,_⟩ := order9_twelve_stage_chart ha ho
  obtain ⟨P,dP,pn,_,hF,fit⟩ := two_curve_head h3 h4 (by omega)
  obtain ⟨fg⟩ := order9_actual_five_six_FG ha ho N M dP pn hF fit
  let h := nodes A (lowPrefix10 fg.first)
  let r := nodes A (lowPrefix10 fg.middle)
  let u := nodes A (lowPrefix10 (8:Fin 10))
  let v := nodes A (lowPrefix10 (Fin.last 9))
  let l := fg.pencil_parameter
  obtain ⟨rEq,kz⟩ := fg.compatibility_zero
  have er : r=2-l-h-u-v := rEq
  refine ⟨h,u,v,l,?_,?_,kz,fg.terminal_product_zero ha ho N M hF dP pn fit⟩
  · rw [←er]
    exact fg.root_set_injective
  · rw [←er]
    exact fg.pencil_roots

end Ordered
end RKCert.Paired
