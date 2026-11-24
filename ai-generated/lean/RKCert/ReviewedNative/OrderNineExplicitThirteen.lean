module
public import RKCert.ReviewedNative.OrderNineSixOnOffEighth
public import RKCert.ReviewedNative.OrderNineSixOnCollision

@[expose] public section

/-! # Native ordered explicit order-nine stage floor, fully discharged -/
namespace RKResearch.Certified.Graded.MultiOff
open RKResearch Module Polynomial OneOff Reverse RKCert.Endpoint
open scoped Matrix Classical
variable {K : Type*} [Field K] 

variable [LinearOrder K] [IsStrictOrderedRing K]
theorem ActualSixOnFG.prefix_on_hull
    {A : Matrix (Fin 12) (Fin 12) K} {b : (Fin 12→K)}
    (ha : ∀i j,i≤j → A i j=0) (ho : HasOrder A b 9)
    (N : (offKnots A).card=5) (M : (cleanKnots A).card=6)
    {P : K[X]} (fit : ∀i,OneOff.g A i≠0 → P.eval (nodes A i)=OneOff.g A i)
    (fg : ActualSixOnFG A P) :
    nodalHull (RKCert.Paired.endpointErase (cleanKnots A) 1)=X*RKCert.Paired.lobattoPencil fg.pencil_parameter := by
  let _ : DecidableEq K := fun _ _ => Classical.propDecidable _
  obtain ⟨_,_,_,hc,he,_,last⟩ := order9_five_six_stage_chart ha ho N M fit
  let T := RKCert.Paired.endpointErase (cleanKnots A) 1
  let S := RKCert.Paired.endpointErase T 0
  have one : (1:K)∈cleanKnots A := mem_cleanKnots.mpr ⟨_,hc,he⟩
  have zero : (0:K)∈T := Finset.mem_erase.mpr ⟨zero_ne_one,zero_mem_cleanKnots ha⟩
  have Ts : T.card+1=(cleanKnots A).card := Finset.card_erase_add_one one
  have Ss : S.card+1=T.card := Finset.card_erase_add_one zero
  have cS : S.card=4 := by omega
  let W : Fin 4→K := ![nodes A (lowPrefix10 fg.first),nodes A (lowPrefix10 fg.middle),
    nodes A (lowPrefix10 (8:Fin 10)),nodes A (lowPrefix10 (Fin.last 9))]
  let U := Finset.univ.image W
  have cU : U.card=4 := by
    simp only [U,Finset.card_image_of_injective _ (show Function.Injective W from fg.root_set_injective),
      Finset.card_univ,Fintype.card_fin]
  have mem (i : Fin 10) (gi : OneOff.g A (lowPrefix10 i)=0) (z : nodes A (lowPrefix10 i)≠0) :
      nodes A (lowPrefix10 i)∈S :=
    Finset.mem_erase.mpr ⟨z,Finset.mem_erase.mpr ⟨first_prefix_clean_value_ne_one last i gi,
      mem_cleanKnots.mpr ⟨_,gi,rfl⟩⟩⟩
  have su : U⊆S := by
    intro x hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    fin_cases i
    · exact mem _ fg.first_clean fg.first_nonzero
    · exact mem _ fg.middle_clean fg.middle_nonzero
    · exact mem _ fg.late_u_clean fg.late_u_nonzero
    · exact mem _ fg.late_v_clean fg.late_v_nonzero
  have eU : U=S := Finset.eq_of_subset_of_card_le su (by omega)
  let Q := RKCert.Paired.lobattoPencil fg.pencil_parameter
  obtain ⟨t,e⟩ := RKCert.Paired.polynomial_scalar_hull S Q
    (by change (RKCert.Paired.lobattoPencil fg.pencil_parameter).natDegree≤S.card; rw [RKCert.Paired.lobattoPencil_natDegree,cS]) (by
      intro x hx
      rw [←eU] at hx
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
      exact fg.pencil_roots i)
  have hC : (nodalHull S : K[X]).coeff 4=1 := by
    rw [←(natDegree_nodalHull (K:=K) S).trans cS]
    exact (monic_nodalHull S).coeff_natDegree
  have t1 : t=1 := by
    have a := congrArg (fun P : K[X]=>P.coeff 4) e
    simpa [Q,RKCert.Paired.lobattoPencil,coeff_monomial,coeff_C_mul,hC] using a.symm
  have f : Q=nodalHull S := by simpa [t1] using e
  change nodalHull T=X*Q
  rw [RKCert.Paired.nodalHull_erase_factor T zero,map_zero,sub_zero,f]

theorem ActualSixOnFG.hat_scale {A : Matrix (Fin 12) (Fin 12) K} {P : K[X]} (fg : ActualSixOnFG A P) :
    let h := nodes A (lowPrefix10 fg.first)
    let u := nodes A (lowPrefix10 (8:Fin 10))
    let v := nodes A (lowPrefix10 (Fin.last 9))
    let H := RKCert.Paired.sixOnHat h u v
    H.coeff 2≠0 → ∃ a : K,a≠0 ∧ H=C a*P ∧ H.natDegree=2 ∧ P.natDegree=2 := by
  dsimp only
  intro n
  let h := nodes A (lowPrefix10 fg.first)
  let u := nodes A (lowPrefix10 (8:Fin 10))
  let v := nodes A (lowPrefix10 (Fin.last 9))
  let H := RKCert.Paired.sixOnHat h u v
  let f₀ := RKCert.Paired.sixOnF u v (RKCert.Paired.fixedRadauP0 h)
  let f₁ := RKCert.Paired.sixOnF u v (RKCert.Paired.fixedRadauP1 h)
  let t := fg.affine_parameter
  let a := fg.head_scale
  have z : f₀+t*f₁=0 := by
    have z := fg.F_zero
    change RKCert.Paired.sixOnF u v (fun x=>RKCert.Paired.fixedRadauP0 h x+t*RKCert.Paired.fixedRadauP1 h x)=0 at z
    dsimp only [f₀,f₁]
    unfold RKCert.Paired.sixOnF at z ⊢
    linear_combination z
  have e : f₀= -t*f₁ := by linear_combination z
  have fn : f₁≠0 := by
    intro e1
    have e0 : f₀=0 := by simp [e,e1]
    have hZ : H=0 := by
      change C f₁*RKCert.Paired.sixOnP0 h-C f₀*RKCert.Paired.sixOnP1 h=0
      rw [e0,e1,map_zero,zero_mul,zero_mul,sub_self]
    exact n (by change H.coeff 2=0; simp [hZ])
  have da : f₁/a≠0 := div_ne_zero fn fg.head_scale_nonzero
  have er : H=C (f₁/a)*P := by
    let _ : Infinite K := Infinite.of_injective (fun n : ℕ => (n:K)) Nat.cast_injective
    apply Polynomial.funext
    intro x
    change (C f₁*RKCert.Paired.sixOnP0 h-C f₀*RKCert.Paired.sixOnP1 h).eval x=(C (f₁/a)*P).eval x
    rw [eval_sub,eval_mul,eval_mul,eval_mul,eval_C,eval_C,eval_C,
      RKCert.Paired.sixOnP0_eval,RKCert.Paired.sixOnP1_eval,fg.head_shape,e]
    have ka : f₁/a*a=f₁ := div_mul_cancel₀ _ fg.head_scale_nonzero
    change _=f₁/a*(a*(RKCert.Paired.fixedRadauP0 h x+t*RKCert.Paired.fixedRadauP1 h x))
    rw [←mul_assoc,ka]
    ring
  have dH : H.natDegree=2 := natDegree_eq_of_le_of_coeff_ne_zero (RKCert.Paired.sixOnHat_degree _ _ _) n
  have dP : P.natDegree=2 := by
    have d := dH
    rw [er,natDegree_C_mul da] at d
    exact d
  exact ⟨f₁/a,da,er,dH,dP⟩

set_option maxHeartbeats 1200000 in
/-- Terminal product zero is forced by an actual (5,6) tableau,
including the linear and all three physical stage-placement cases. -/
theorem ActualSixOnFG.terminal_product_zero
    {A : Matrix (Fin 12) (Fin 12) K} {b : (Fin 12→K)}
    (ha : ∀i j,i≤j → A i j=0) (ho : HasOrder A b 9)
    (N : (offKnots A).card=5) (M : (cleanKnots A).card=6)
    (hF : zeroSpace A 4=band A 2)
    {P : K[X]} (dP : P.natDegree≤2) (pn : P≠0)
    (fit : ∀i,OneOff.g A i≠0 → P.eval (nodes A i)=OneOff.g A i)
    (fg : ActualSixOnFG A P) :
    RKCert.Paired.sixOnTerminalProduct (nodes A (lowPrefix10 fg.first)) (nodes A (lowPrefix10 (8:Fin 10)))
      (nodes A (lowPrefix10 (Fin.last 9))) fg.pencil_parameter=0 := by
  let h := nodes A (lowPrefix10 fg.first)
  let u := nodes A (lowPrefix10 (8:Fin 10))
  let v := nodes A (lowPrefix10 (Fin.last 9))
  let l := fg.pencil_parameter
  let H := RKCert.Paired.sixOnHat h u v
  let Q := X*RKCert.Paired.lobattoPencil l
  change H.coeff 2*RKCert.Paired.sixOnO5 h u v l*RKCert.Paired.sixOnO6 h u v l*RKCert.Paired.sixOnHc h u v=0
  by_cases zero : H.coeff 2=0
  · rw [zero,zero_mul,zero_mul,zero_mul]
  by_cases on : OneOff.g A (lowPrefix10 (7:Fin 10))=0
  · rw [show RKCert.Paired.sixOnHc h u v=0 from order9_actual_five_six_on_eighth_atlas ha ho N M hF dP fit fg on,
      mul_zero]
  obtain ⟨a,an,er,dH,dP'⟩ := fg.hat_scale zero
  change H=C a*P at er
  have q : nodalHull (RKCert.Paired.endpointErase (cleanKnots A) 1)=Q := fg.prefix_on_hull ha ho N M fit
  have dQ : Q.natDegree≤5 := by
    have z := natDegree_mul_le_of_le (show (X:K[X]).natDegree≤1 by simp) (RKCert.Paired.lobattoPencil_natDegree l).le
    exact z
  have dH' : H.natDegree≤2 := dH.le
  have div : H∣P := ⟨C a⁻¹,by
    rw [er]
    calc P=C (a*a⁻¹)*P := by rw [mul_inv_cancel₀ an,map_one,one_mul]
      _=(C a*P)*C a⁻¹ := by rw [map_mul]; ring⟩
  obtain ⟨_,_,place⟩ := order9_actual_five_six_off_eighth ha ho N M hF dP' pn fit fg on
  rcases place with ⟨_,t,_,z⟩|⟨_,t,_,z⟩
  · let U := RKCert.Paired.sixOnPort u v*(X^2*(X-C h)^2)
    have dU : U.natDegree≤5 := by
      have a1 : (X^2:K[X]).natDegree≤2 := natDegree_X_pow_le _
      have a2 : ((X-C h)^2).natDegree≤2 := natDegree_pow_le_of_le _ (show (X-C h).natDegree≤1 by simp)
      exact natDegree_mul_le_of_le (RKCert.Paired.sixOnPort_degree _ _) (natDegree_mul_le_of_le a1 a2)
    rw [q] at z
    have e := RKCert.Paired.quadraticPremDet_zero_of_dvd dH dU dQ (div.trans z)
    change RKCert.Paired.sixOnO5 h u v l=0 at e
    rw [e,mul_zero,zero_mul,zero_mul]
  · let D := RKCert.Paired.sixOnPort u v
    let U := D*RKCert.Paired.primitive (X*H)
    have dU : U.natDegree≤5 := by
      have e : (X*H).natDegree≤3 := natDegree_mul_le_of_le (by simp) dH'
      exact natDegree_mul_le_of_le (RKCert.Paired.sixOnPort_degree _ _) (RKCert.Paired.primitive_natDegree_le e)
    have es : U=C a*(D*RKCert.Paired.primitive (X*P)) := by
      change D*RKCert.Paired.primitive (X*H)=_
      rw [er]
      have ex : X*(C a*P)=C a*(X*P) := by ring
      rw [ex,←smul_eq_C_mul,map_smul,smul_eq_C_mul]
      ring
    have ep : C (t/a)*U=C t*(D*RKCert.Paired.primitive (X*P)) := by
      rw [es,←mul_assoc,←map_mul,div_mul_cancel₀ _ an]
    rw [q] at z
    rw [←scalar_primitive (X*P)] at z
    change P∣Q-C t*(D*RKCert.Paired.primitive (X*P)) at z
    rw [←ep] at z
    have e := RKCert.Paired.quadraticPremDet_zero_of_dvd dH dU dQ (div.trans z)
    change RKCert.Paired.sixOnO6 h u v l=0 at e
    rw [e,mul_zero,zero_mul]

/-- Complete physical interface for the remaining two-curve atlas.
The separate scalar norm/gcd exclusion is not asserted here. -/
theorem order9_actual_five_six_atlas_input
    {A : Matrix (Fin 12) (Fin 12) K} {b : (Fin 12→K)}
    (ha : ∀i j,i≤j → A i j=0) (ho : HasOrder A b 9)
    (N : (offKnots A).card=5) (M : (cleanKnots A).card=6) :
    ∃ h u v l : K,
      let W : Fin 4→K := ![h,2-l-h-u-v,u,v]
      Function.Injective W ∧ (∀i,(RKCert.Paired.lobattoPencil l).eval (W i)=0) ∧
        RKCert.Paired.sixOnK8 h u v l=0 ∧ RKCert.Paired.sixOnTerminalProduct h u v l=0 := by
  obtain ⟨P,dP,pn,_,hF,fit⟩ := order9_two_curve_head ha ho (by decide) (by omega)
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



/-- The last physical chart contradicts the already checked scalar atlas.
This theorem and all physical predecessors use the original tableau and
`RKResearch.HasOrder`, not a duplicate tree or order representation. -/
theorem order9_no_five_off_six_on
    {A : Matrix (Fin 12) (Fin 12) K} {b : Fin 12→K}
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder A b 9)
    (off : (offKnots A).card=5) (on : (cleanKnots A).card=6) : False := by
  obtain ⟨h,u,v,l,inj,roots,k,prod⟩ := order9_actual_five_six_atlas_input ha ho off on
  exact six_on_witness_impossible inj roots k prod

/-- Every strictly lower explicit Runge–Kutta tableau satisfying the
reviewed rooted-tree conditions through order nine over an ordered field
has at least thirteen stages. No restrictions on stage coincidences,
weights, or clock ordering are required. -/
theorem explicit_order_nine_at_least_thirteen {s : ℕ}
    {A : Matrix (Fin s) (Fin s) K} {b : Fin s→K}
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder A b 9) : 13≤s := by
  by_contra! small
  have size := (order9_forward_chart ha ho (by omega)).1
  subst s
  obtain ⟨off,on⟩ := order9_five_six_remaining ha ho
  exact order9_no_five_off_six_on ha ho off on
end RKResearch.Certified.Graded.MultiOff
