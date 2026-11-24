module
public import RKCert.SplitFactorGate
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.Derivative

@[expose] public section
namespace RKCert.FixedFactor
open Polynomial
universe u v
variable {ι : Type v}

/-- Evaluation with integer coefficients is natural under every unital ring map. -/
noncomputable def zEval {S : Type*} [CommRing S] (P : MvPolynomial ι ℤ) (w : ι→S) : S :=
  MvPolynomial.eval₂Hom (Int.castRingHom S) w P

theorem map_zEval {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (P : MvPolynomial ι ℤ) (w : ι→R) : φ (zEval P w)=zEval P (fun i=>φ (w i)) := by
  simp only [zEval,MvPolynomial.map_eval₂Hom]
  congr 2
  exact Subsingleton.elim ..

/-- A pair of genuinely distinct roots of a polynomial over a domain cannot
collide under a map at a *simple* root of the reduced polynomial. This is why
inequalities between the original nodes can be retained in a split-prime table. -/
theorem distinct_at_simple_image {R S : Type*} [CommRing R] [IsDomain R] [Field S]
    (φ : R →+* S) (H : R[X]) (x y : R) (hx : H.eval x=0) (hy : H.eval y=0)
    (hne : x≠y) (hs : (H.map φ).derivative.eval (φ x)≠0) : φ x ≠ φ y := by
  obtain ⟨T,hT⟩ := dvd_iff_isRoot.mpr hx
  have t0 : T.eval y=0 := by
    rw [hT,eval_mul,eval_sub,eval_X,eval_C] at hy
    exact (mul_eq_zero.mp hy).resolve_left (sub_ne_zero.mpr hne.symm)
  intro e
  apply hs
  rw [hT,Polynomial.map_mul,Polynomial.map_sub,map_X,map_C,derivative_mul]
  simp only [eval_add,eval_mul,eval_sub,eval_X,eval_C,sub_self,zero_mul,add_zero]
  rw [e,Polynomial.eval_map_apply,t0,map_zero,mul_zero]

theorem int_comp {S T : Type*} [CommRing S] [CommRing T] (f : S→+*T) :
    f.comp (Int.castRingHom S)=Int.castRingHom T := Subsingleton.elim ..

/-- Extend a squarefree split-prime finite test to an arbitrary characteristic-
zero field. `mask` specifies exactly which pairs of coordinates need to remain
distinct. The tested expression is an actual multivariate integer polynomial. -/
theorem split_prime_root_tuple {K : Type u} [Field K] [CharZero K] (p : ℕ) [Fact p.Prime]
    (H : ℤ[X]) (mon : H.Monic) (knots : List (ZMod p))
    (split : H.map (Int.castRingHom (ZMod p))=linearProduct id knots)
    (simple : ∀z∈knots, (H.map (Int.castRingHom (ZMod p))).derivative.eval z≠0)
    (test : MvPolynomial ι ℤ) (mask : ι→ι→Prop)
    (check : ∀z : ι→ZMod p, (∀i, z i∈knots) → (∀i j, mask i j → z i≠z j) →
      zEval test z≠0)
    (w : ι→K) (roots : ∀i, (H.map (Int.castRingHom K)).eval (w i)=0)
    (distinct : ∀i j, mask i j → w i≠w j) : zEval test w≠0 := by
  classical
  intro hz
  let O:=integralClosure ℤ K
  let inc : O→+*K := (integralClosure ℤ K).val.toRingHom
  have hi : Function.Injective inc := Subtype.coe_injective
  have integral (i : ι) : IsIntegral ℤ (w i) := ⟨H,mon,by rw [eval₂_eq_eval_map,algebraMap_int_eq]; exact roots i⟩
  let w' : ι→O:=fun i=>⟨w i,integral i⟩
  have rootO (i : ι) : (H.map (Int.castRingHom O)).eval (w' i)=0 := by
    apply hi
    rw [map_zero,←Polynomial.eval_map_apply,map_map,int_comp inc]
    exact roots i
  have zO : zEval test w'=0 := by
    apply hi
    rw [map_zero,map_zEval]
    exact hz
  let I := RingHom.ker (Int.castRingHom (ZMod p))
  let : I.IsMaximal := RingHom.ker_isMaximal_of_surjective (Int.castRingHom (ZMod p)) ZMod.intCast_surjective
  obtain ⟨J,jm,over⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S:=O) I (by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp (Int.cast_injective (α:=O))]; exact bot_le)
  let : J.IsMaximal := jm
  let E := O ⧸ J
  let : Field E := Ideal.Quotient.field J
  let φ := Ideal.Quotient.mk J
  have hp0 : (p:E)=0 := by
    change φ (p:O)=0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    have beneath : (p:ℤ)∈J.under ℤ := by
      rw [over]; change ((p:ℤ):ZMod p)=0; simp
    simpa only [algebraMap_int_eq,Int.coe_castRingHom,Int.cast_natCast] using ((Ideal.mem_under ℤ J).mp beneath)
  let : CharP E p := (CharP.charP_iff_prime_eq_zero (R:=E) (Fact.out : p.Prime)).mpr hp0
  let ψ:=ZMod.castHom (dvd_refl p) E
  have hs : H.map (Int.castRingHom E)=linearProduct ψ knots := by
    rw [←int_comp ψ,←map_map,split,map_product]; rfl
  have atRoot (i : ι) : (H.map (Int.castRingHom E)).eval (φ (w' i))=0 := by
    rw [←int_comp φ,←map_map,Polynomial.eval_map_apply,rootO,map_zero]
  have rep (i : ι) : ∃z∈knots, φ (w' i)=ψ z := endpoint_of_product _ _ _ (hs ▸ atRoot i)
  choose z mem ze using rep
  have simple' (i : ι) : ((H.map (Int.castRingHom O)).map φ).derivative.eval (φ (w' i))≠0 := by
    rw [map_map,int_comp φ,←int_comp ψ,←map_map,derivative_map,ze,Polynomial.eval_map_apply]
    exact fun e=>simple _ (mem i) (ψ.injective (e.trans ψ.map_zero.symm))
  have distinct' (i j : ι) (h : mask i j) : z i≠z j := by
    intro eq
    apply distinct_at_simple_image φ _ _ _ (rootO i) (rootO j)
      (fun e => distinct i j h (congrArg inc e)) (simple' i)
    rw [ze,ze,eq]
  apply check z mem distinct'
  apply ψ.injective
  rw [ψ.map_zero,map_zEval]
  change zEval test (fun i=>ψ (z i))=0
  simpa only [map_zEval,ze,map_zero] using congrArg φ zO

theorem product_eval_of_mem {E : Type*} [Field E] (l : List E) {a : E} (h:a∈l) :
    (linearProduct id l).eval a=0 := by
  induction l with
  | nil => simp at h
  | cons x l ih =>
    rcases List.mem_cons.mp h with rfl|hl <;> simp [linearProduct, *]

theorem simple_product_of_nodup {E : Type*} [Field E] (l : List E) (hn:l.Nodup)
    {a : E} (h:a∈l) : (linearProduct id l).derivative.eval a≠0 := by
  induction l with
  | nil => simp at h
  | cons x l ih =>
    obtain ⟨hx,ht⟩:=List.nodup_cons.mp hn
    simp only [linearProduct,derivative_mul,derivative_sub,derivative_X,derivative_C,sub_zero,
      one_mul,eval_add,eval_mul,eval_sub,eval_X,eval_C,id_eq]
    rcases List.mem_cons.mp h with rfl|hl
    · rw [sub_self,zero_mul,add_zero]
      intro zero
      obtain ⟨b,hb,eb⟩:=endpoint_of_product id l _ zero
      exact hx (eb ▸ hb)
    · rw [product_eval_of_mem l hl,zero_add]
      exact mul_ne_zero (sub_ne_zero.mpr (fun e=>hx (e ▸ hl))) (ih ht hl)

end RKCert.FixedFactor
