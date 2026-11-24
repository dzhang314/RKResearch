module

public import RKCert.DirkHermite

@[expose] public section

/-! # Two origin jets versus five genuine dirty stage sites

Only the resulting five scalar trace equations are used here. The earlier
chronological reduction is not built into this algebraic contradiction. -/
namespace RKCert.Endpoint
open Polynomial Module
open scoped Classical
variable {K : Type*} [Field K]

theorem ofFn_coeff_recover (P : K[X]) {n : ℕ} (h : P.natDegree<n) :
    ofFn n (fun i => P.coeff i.val) = P := by
  ext j
  by_cases hj : j<n
  · rw [ofFn_coeff_eq_val_of_lt _ hj]
  · rw [ofFn_coeff_eq_zero_of_ge _ (by omega),coeff_eq_zero_of_natDegree_lt (by omega)]

theorem origin_jet_eq_of_no_certificate [CharZero K] {P : K[X]} (P0 : P.eval 0=0)
    (P'0 : P.derivative.eval 0=0) {n : ℕ} (z : Fin n → K) (hz : Function.Injective z)
    (he : ∀ i, P.eval (z i)=0) (hdeg : P.natDegree≤n) : P=0 := by
  by_cases hP : P=0
  · exact hP
  have hx : X ∣ P := by
    rw [X_dvd_iff,coeff_zero_eq_eval_zero]
    exact P0
  obtain ⟨G,hG⟩ := hx
  have hg0 : G.eval 0=0 := by
    simpa only [hG,derivative_mul,derivative_X,eval_add,eval_mul,
      eval_one,eval_X,one_mul,zero_mul,add_zero] using P'0
  have hGne : G≠0 := by intro e; simp [hG,e] at hP
  have hg : G.natDegree<n := by
    rw [hG,natDegree_mul X_ne_zero hGne,natDegree_X] at hdeg
    omega
  have hv (i : Fin n) : G.eval (z i)=0 := by
    by_cases hi : z i=0
    · simpa [hi] using hg0
    · have hv := he i
      rw [hG,eval_mul,eval_X] at hv
      exact (mul_eq_zero.mp hv).resolve_left hi
  have heq := eq_zero_of_natDegree_lt_card_of_eval_eq_zero G hz hv (by simpa using hg)
  simp [hG,heq]

theorem equal_on_knots_of_same_degree (S : Finset K) {F G : K[X]}
    (hF : F.natDegree≤S.card) (hG : G.natDegree≤S.card)
    (he : ∀ a∈S, F.eval a=G.eval a) :
    ∃ a : K, F-G=nodalHull S * C a := by
  by_cases h : F-G=0
  · exact ⟨0,by simp [h]⟩
  have hdvd : nodalHull S ∣ F-G := by
    unfold nodalHull
    apply Finset.prod_dvd_of_coprime
    · intro a _ b _ hab
      exact isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hab).isUnit
    · intro a ha
      apply dvd_iff_isRoot.mpr
      simpa only [IsRoot.def,eval_sub,sub_eq_zero] using he a ha
  obtain ⟨R,hR⟩ := hdvd
  have hRne : R≠0 := fun e => h (by simp [hR,e])
  have hsub := natDegree_sub_le (p:=F) (q:=G)
  rw [hR,natDegree_mul (monic_nodalHull S).ne_zero hRne,natDegree_nodalHull] at hsub
  have d0 : R.natDegree=0 := by omega
  exact ⟨R.coeff 0, hR.trans (congrArg _ (eq_C_of_natDegree_eq_zero d0))⟩

variable [CharZero K]

theorem five_dirty_origin_jets (z : Fin 5 → K) (hz : Function.Injective z)
    (P : K[X]) (hd : P.natDegree≤3) (hP0 : P.eval 0≠0)
    (hP : ∀ i, P.eval (z i)≠0)
    (hflow : ∀ f q : K[X], f.natDegree≤4 → f.eval 0=0 → q.natDegree≤1 →
      (∀ i : Fin 3, f.eval (z (Fin.castLE (by decide) i)) +
        P.eval (z (Fin.castLE (by decide) i))*q.eval (z (Fin.castLE (by decide) i))=0) →
      ∃ r : K[X], r.natDegree≤2 ∧
        ∀ i, (formalPrimitive f).eval (z i)=P.eval (z i)*r.eval (z i)) : False := by
  classical
  let test : K[X] →ₗ[K] (Fin 5 → K) := LinearMap.pi (fun i => leval (z i))
  let low : K[X] →ₗ[K] (Fin 3 → K) := LinearMap.pi (fun i => leval (z (Fin.castLE (by decide) i)))
  let F := (LinearMap.mulLeft K (X:K[X])).comp (ofFn 4)
  let G := (LinearMap.mulLeft K P).comp (ofFn 2)
  let prefixMap := (low.comp F).coprod (low.comp G)
  let D := LinearMap.ker prefixMap
  let image := ((test.comp formalPrimitiveLinear).comp F).comp
    ((LinearMap.fst K (Fin 4 → K) (Fin 2 → K)).comp D.subtype)
  let band := (test.comp (LinearMap.mulLeft K P)).comp (ofFn 3)
  have rankD : 3≤finrank K D := by
    have hb := Submodule.finrank_le (LinearMap.range prefixMap)
    have hdim := prefixMap.finrank_range_add_finrank_ker
    have h₁ : finrank K (Fin 3 → K)=3 := by simp
    have h₂ : finrank K ((Fin 4 → K) × (Fin 2 → K))=6 := by simp [Module.finrank_prod]
    change _ + finrank K D = _ at hdim
    rw [h₁] at hb
    rw [h₂] at hdim
    omega
  have hF (a : Fin 4 → K) : (F a).natDegree≤4 := by
    have h := natDegree_mul_le (p:=(X:K[X])) (q:=ofFn 4 a)
    have h' := ofFn_natDegree_lt (by decide : 0<4) a
    rw [natDegree_X] at h
    change (X*ofFn 4 a).natDegree≤4
    omega
  have hF0 (a : Fin 4 → K) : (F a).eval 0=0 := by change (X*ofFn 4 a).eval 0=0; simp
  have atPrefix (v : D) (i : Fin 3) :
      (F v.val.1).eval (z (Fin.castLE (by decide) i)) +
        P.eval (z (Fin.castLE (by decide) i))*(ofFn 2 v.val.2).eval (z (Fin.castLE (by decide) i))=0 := by
    have hp : prefixMap v.val=0 := v.property
    have hr := congrFun hp i
    change (F v.val.1).eval (z (Fin.castLE (by decide) i)) +
      (P*ofFn 2 v.val.2).eval (z (Fin.castLE (by decide) i))=0 at hr
    simpa only [eval_mul] using hr
  have contain : LinearMap.range image≤LinearMap.range band := by
    rintro _ ⟨v,rfl⟩
    obtain ⟨r,hr,hEq⟩ := hflow (F v.val.1) (ofFn 2 v.val.2) (hF _) (hF0 _)
      (by have := ofFn_natDegree_lt (by decide : 0<2) v.val.2; omega) (atPrefix v)
    refine ⟨fun i => r.coeff i.val,?_⟩
    ext i
    change (P*ofFn 3 (fun i => r.coeff i.val)).eval (z i) =
      (formalPrimitive (F v.val.1)).eval (z i)
    rw [ofFn_coeff_recover r (by omega),eval_mul, hEq]
  have hinj : Function.Injective image := by
    apply (injective_iff_map_eq_zero _).mpr
    intro v he
    let J := formalPrimitive (F v.val.1)
    have hJ0 : J.eval 0=0 := formalPrimitive_eval_zero _
    have hJ'0 : J.derivative.eval 0=0 := by simpa [J] using hF0 v.val.1
    have hv (i : Fin 5) : J.eval (z i)=0 := congrFun he i
    have hdeg : J.natDegree≤5 := (natDegree_formalPrimitive_le _).trans (by
      have := hF v.val.1
      omega)
    have hzero := origin_jet_eq_of_no_certificate hJ0 hJ'0 z hz hv hdeg
    have hFzero : F v.val.1=0 := by
      simpa only [J,derivative_formalPrimitive,derivative_zero] using
        congrArg Polynomial.derivative hzero
    have hf : v.val.1=0 := by
      apply injective_ofFn 4
      rw [map_zero]
      change X * ofFn 4 v.val.1=0 at hFzero
      exact (mul_eq_zero.mp hFzero).resolve_left X_ne_zero
    have hg : v.val.2=0 := by
      have hz' : Function.Injective (fun i : Fin 3 => z (Fin.castLE (by decide) i)) :=
        hz.comp (Fin.castLE_injective (by decide))
      have e (i : Fin 3) : (ofFn 2 v.val.2).eval (z (Fin.castLE (by decide) i))=0 := by
        have ha := atPrefix v i
        simp only [hf,map_zero,eval_zero,zero_add] at ha
        exact (mul_eq_zero.mp ha).resolve_left (hP _)
      apply injective_ofFn 2
      rw [map_zero]
      apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hz' e
      have := ofFn_natDegree_lt (by decide : 0<2) v.val.2
      simp only [Fintype.card_fin]
      omega
    exact Subtype.ext (Prod.ext hf hg)
  have rangeEq : LinearMap.range image = LinearMap.range band := by
    apply Submodule.eq_of_le_of_finrank_le contain
    rw [LinearMap.finrank_range_of_inj hinj]
    have h := LinearMap.finrank_range_le band
    have h₃ : finrank K (Fin 3 → K)=3 := by simp
    rw [h₃] at h
    exact h.trans rankD
  have lift (Q : K[X]) (hQ : Q.natDegree≤2) :
      ∃ J : K[X], J.eval 0=0 ∧ J.derivative.eval 0=0 ∧ J.natDegree≤5 ∧
        ∀ i, J.eval (z i) = (P*Q).eval (z i) := by
    let a : Fin 3 → K := fun i => Q.coeff i.val
    have h : band a∈LinearMap.range image := by rw [rangeEq]; exact ⟨a,rfl⟩
    obtain ⟨v,hv⟩ := h
    let J := formalPrimitive (F v.val.1)
    refine ⟨J,formalPrimitive_eval_zero _,by simpa [J] using hF0 v.val.1,
      (natDegree_formalPrimitive_le _).trans (by have := hF v.val.1; omega),fun i => ?_⟩
    have e := congrFun hv i
    change J.eval (z i) = (P*ofFn 3 a).eval (z i) at e
    rwa [ofFn_coeff_recover Q (by omega)] at e
  obtain ⟨J,J0,J'0,Jd,Jz⟩ := lift 1 (by simp)
  obtain ⟨V,V0,V'0,Vd,Vz⟩ := lift X (by simp)
  let S : Finset K := Finset.univ.image z
  have hS : S.card=5 := by simp [S,Finset.card_image_of_injective _ hz]
  have hJ (a : K) (ha : a∈S) : J.eval a=P.eval a := by
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
    simpa using Jz i
  have hV (a : K) (ha : a∈S) : V.eval a=(P*X).eval a := by
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
    exact Vz i
  obtain ⟨u,hu⟩ := equal_on_knots_of_same_degree S (by omega) (by omega) hJ
  obtain ⟨w,hw⟩ := equal_on_knots_of_same_degree S (by omega) (by
    have := natDegree_mul_le (p:=P) (q:=(X:K[X]))
    rw [natDegree_X] at this
    omega) hV
  have val := congrArg (Polynomial.eval 0) hu
  simp only [eval_sub,J0,zero_sub,eval_mul,eval_C] at val
  have hH0 : (nodalHull S).eval 0≠0 := by
    intro e
    rw [e,zero_mul,neg_eq_zero] at val
    exact hP0 val
  have val' := congrArg (Polynomial.eval 0) hw
  simp only [eval_sub,V0,eval_mul,eval_X,mul_zero,sub_zero,eval_C] at val'
  have hw0 : w=0 := (mul_eq_zero.mp val'.symm).resolve_left hH0
  have hvp : V=P*X := by simpa [hw0,sub_eq_zero] using hw
  have deri := congrArg (fun H : K[X] => H.derivative.eval 0) hvp
  simp only [V'0,derivative_mul,derivative_X,eval_add,eval_mul,eval_X,mul_zero,
    zero_add,mul_one] at deri
  exact hP0 deri.symm

end RKCert.Endpoint
