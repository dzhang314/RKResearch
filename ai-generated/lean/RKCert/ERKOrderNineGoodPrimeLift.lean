module

public import RKCert.ERKOrderNineGoodPrimeTransport

@[expose] public section

/-! # Good-prime lifting for the genuinely algebraic endpoint

Only the parameter and the three scalar roots are reduced. This is the
same integral-closure/going-up mechanism as IntegralFactorGate, now over
a localization so both the parameter leading coefficient and 84 are
invertible. The strict tableau and its order conditions are never reduced.
-/
namespace RKCert.GoodPrimeDense
open Polynomial RKCert.FixedFactor

noncomputable def Four.polynomial {R : Type*} [CommRing R] (q : Four R) : R[X] :=
  ofCoeffList [q.a,q.b,q.c,q.d,1]

theorem Four.polynomial_map {R S : Type*} [CommRing R] [CommRing S]
    (q : Four R) (f : R→+*S) : q.polynomial.map f = (q.map f).polynomial := by
  simp [Four.polynomial,map_ofCoeffList,Four.map]

theorem Four.polynomial_eval {R : Type*} [CommRing R] (q : Four R) (x : R) :
    q.polynomial.eval x = q.eval x := by
  simp [Four.polynomial,Four.eval,ofCoeffList_cons]
  ring

theorem Four.polynomial_monic {R : Type*} [CommRing R] (q : Four R) :
    q.polynomial.Monic := by
  apply monic_of_degree_le 4
  · apply (degree_le_iff_coeff_zero _ _).mpr
    intro i hi
    unfold Four.polynomial
    have hi' : 5 ≤ i := Nat.succ_le_of_lt (by exact_mod_cast hi)
    rw [coeff_ofCoeffList,List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simpa only [List.length_cons,List.length_nil] using hi')]
    rfl
  · simp [Four.polynomial]

theorem RootSystem.roots {R : Type*} [CommRing R] {q : Four R} {h u v : R}
    (hs : RootSystem q h u v) : q.eval h=0 ∧ q.eval u=0 ∧ q.eval v=0 := by
  refine ⟨hs.four,?_ ,?_⟩
  · rw [q.eval_div h, hs.four, hs.three, mul_zero, add_zero]
  · rw [q.eval_div h, hs.four, (q.shifted h).eval_div u,hs.three,hs.two]
    ring

universe u

set_option maxHeartbeats 600000 in
theorem endpoint_good_prime {K : Type u} [Field K] [CharZero K]
    (p : ℕ) [Fact p.Prime] (H : ℤ[X])
    (h84 : (84:ZMod p)≠0) (hc : (Int.castRingHom (ZMod p)) H.leadingCoeff≠0)
    (auxiliary : Fin 3 → MvPolynomial (Fin 4) ℤ)
    (certificate : ∀ {E : Type u} [Field E] [CharP E p] (h u v l d : E),
      d*84=1 → (H.map (Int.castRingHom E)).eval l=0 →
      RootSystem (pencilAt l d) h u v →
      (∀j, zEval (auxiliary j) ![l,h,u,v]=0) → terminalAt h u v l d≠0)
    (h u v l : K) (hl : (H.map (Int.castRingHom K)).eval l=0)
    (root : RootSystem (pencilAt l ((84:K)⁻¹)) h u v)
    (vanish : ∀j, zEval (auxiliary j) ![l,h,u,v]=0) :
    terminalAt h u v l ((84:K)⁻¹) ≠ 0 := by
  classical
  intro zero
  let m : ℤ := 84 * H.leadingCoeff
  have hp : (Int.castRingHom (ZMod p)) m≠0 := by
    simpa only [m,map_mul,map_ofNat] using mul_ne_zero h84 hc
  have hm : m≠0 := fun e=>hp (by rw [e,map_zero])
  let R := Localization.Away m
  let km : R→+*K := IsLocalization.Away.lift m (g:=Int.castRingHom K)
    (isUnit_iff_ne_zero.mpr (fun e=>hm (Int.cast_eq_zero.mp e)))
  let μ : R→+*ZMod p := IsLocalization.Away.lift m (g:=Int.castRingHom _)
    (isUnit_iff_ne_zero.mpr hp)
  let : Algebra R K := km.toAlgebra
  have intR : algebraMap ℤ R = Int.castRingHom R := Subsingleton.elim ..
  have km_int : km.comp (Int.castRingHom R) = Int.castRingHom K := Subsingleton.elim ..
  have ki : Function.Injective km := by
    apply (IsLocalization.injective_iff_map_algebraMap_eq
      (M:=Submonoid.powers m) km).mpr
    intro a b
    constructor
    · exact congrArg km
    · intro e
      have ea : km (algebraMap ℤ R a) = (a:K) := by simp [km]
      have eb : km (algebraMap ℤ R b) = (b:K) := by simp [km]
      rw [ea,eb] at e
      exact congrArg (algebraMap ℤ R) (Int.cast_injective e)
  have μs : Function.Surjective μ := by
    intro a
    obtain ⟨b, hb⟩ := ZMod.intCast_surjective a
    exact ⟨algebraMap ℤ R b, by simpa [μ] using hb⟩
  let O := integralClosure R K
  let inc : O→+*K := (integralClosure R K).val.toRingHom
  have ii : Function.Injective inc := Subtype.coe_injective
  have oa : inc.comp (algebraMap R O) = km := rfl
  have oi : Function.Injective (algebraMap R O) := fun a b e =>
    ki (by simpa only [←oa,RingHom.comp_apply] using congrArg inc e)
  have dU : IsUnit (algebraMap ℤ R 84) := IsLocalization.Away.isUnit_of_dvd m ⟨_,rfl⟩
  let dr : R := ↑(dU.unit⁻¹)
  have dmul : dr*(84:R)=1 := by
    have e : (↑dU.unit : R) = (84:R) := by
      calc
        (↑dU.unit:R) = algebraMap ℤ R 84 := dU.unit_spec
        _ = (84:R) := by rw [intR]; norm_num
    calc
      dr * (84:R) = dr * (↑dU.unit:R) := congrArg (dr * ·) e.symm
      _ = 1 := Units.inv_mul _
  let dO : O := algebraMap R O dr
  have dO_mul : dO*(84:O)=1 := by
    change algebraMap R O dr * 84 = 1
    simpa only [map_mul,map_ofNat,map_one] using congrArg (algebraMap R O) dmul
  have dO_apply : inc dO=((84:K)⁻¹) := by
    apply mul_right_cancel₀ (by norm_num : (84:K)≠0)
    rw [inv_mul_cancel₀ (by norm_num : (84:K)≠0)]
    simpa only [map_mul,map_ofNat,map_one] using congrArg inc dO_mul
  have eU : IsUnit (algebraMap ℤ R H.leadingCoeff) :=
    IsLocalization.Away.isUnit_of_dvd m ⟨84,by simp [m,mul_comm]⟩
  let HR := H.map (Int.castRingHom R)
  have le : HR.leadingCoeff = algebraMap ℤ R H.leadingCoeff := by
    have nz : (Int.castRingHom R) H.leadingCoeff≠0 := by
      intro z
      apply hc
      have e : μ.comp (Int.castRingHom R) = Int.castRingHom (ZMod p) := Subsingleton.elim ..
      rw [←e,RingHom.comp_apply,z,map_zero]
    simpa only [HR,intR] using
      (leadingCoeff_map_of_leadingCoeff_ne_zero _ nz)
  let M := C (↑(eU.unit⁻¹):R)*HR
  have mon : M.Monic := monic_C_mul_of_mul_leadingCoeff_eq_one (by
    change (↑(eU.unit⁻¹):R)*HR.leadingCoeff=1
    rw [le]
    calc
      (↑(eU.unit⁻¹):R)*algebraMap ℤ R H.leadingCoeff =
          (↑(eU.unit⁻¹):R)*(↑eU.unit:R) := congrArg ((↑(eU.unit⁻¹):R) * ·) eU.unit_spec.symm
      _ = 1 := Units.inv_mul _)
  have lIntegral : IsIntegral R l := by
    refine ⟨M,mon,?_⟩
    rw [eval₂_eq_eval_map]
    simp only [M,HR,Polynomial.map_mul,map_C,map_map,eval_mul,eval_C]
    change km (↑(eU.unit⁻¹):R) * (H.map (km.comp (Int.castRingHom R))).eval l = 0
    rw [km_int,hl,mul_zero]
  let lO : O := ⟨l,lIntegral⟩
  let qO := pencilAt lO dO
  have qoe : qO.map inc = pencilAt l ((84:K)⁻¹) := by
    change (pencilAt lO dO).map inc = _
    rw [map_pencilAt inc lO dO, dO_apply]
    rfl
  have qint (a : K) (ha : (pencilAt l ((84:K)⁻¹)).eval a=0) : IsIntegral R a := by
    apply isIntegral_trans (A:=O) a
    refine ⟨qO.polynomial,qO.polynomial_monic,?_⟩
    rw [eval₂_eq_eval_map]
    change (qO.polynomial.map inc).eval a=0
    rw [Four.polynomial_map qO inc,qoe,Four.polynomial_eval,ha]
  let hO : O := ⟨h,qint _ root.roots.1⟩
  let uO : O := ⟨u,qint _ root.roots.2.1⟩
  let vO : O := ⟨v,qint _ root.roots.2.2⟩
  have rootO : RootSystem qO hO uO vO := by
    have h₀ : RootSystem (qO.map inc) (inc hO) (inc uO) (inc vO) := qoe.symm ▸ root
    constructor
    · apply ii; simpa [Four.map,Four.eval] using h₀.four
    · apply ii; simpa [Four.map,Four.shifted,Three.eval] using h₀.three
    · apply ii; simpa [Four.map,Four.shifted,Three.shifted,Two.eval] using h₀.two
  have termO : terminalAt hO uO vO lO dO=0 := by
    apply ii
    rw [map_zero,map_terminalAt inc hO uO vO lO dO,dO_apply]
    exact zero
  have auxO (j : Fin 3) : zEval (auxiliary j) ![lO,hO,uO,vO]=0 := by
    apply ii
    rw [map_zero,map_zEval inc (auxiliary j) (![lO,hO,uO,vO] : Fin 4→O)]
    have vectors : (fun i : Fin 4 => inc ((![lO,hO,uO,vO] : Fin 4→O) i)) = ![l,h,u,v] := by
      funext i
      fin_cases i <;> rfl
    rw [vectors]
    exact vanish j
  have lrootO : (H.map (Int.castRingHom O)).eval lO=0 := by
    apply ii
    rw [map_zero,←Polynomial.eval_map_apply,map_map]
    have f : inc.comp (Int.castRingHom O)=Int.castRingHom K := Subsingleton.elim ..
    rw [f]
    exact hl
  let I := RingHom.ker μ
  let : I.IsMaximal := RingHom.ker_isMaximal_of_surjective μ μs
  obtain ⟨J,jm,over⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S:=O) I (by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp oi]; exact bot_le)
  let : J.IsMaximal := jm
  let E := O ⧸ J
  let : Field E := Ideal.Quotient.field J
  let φ := Ideal.Quotient.mk J
  have ep : (p:E)=0 := by
    change φ (p:O)=0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    have base : (p:R) ∈ J.under R := by
      rw [over]
      change μ (p:R)=0
      rw [map_natCast,ZMod.natCast_self]
    simpa only [map_natCast] using (Ideal.mem_under R J).mp base
  let : CharP E p := (CharP.charP_iff_prime_eq_zero (R:=E) (Fact.out : p.Prime)).mpr ep
  have z := congrArg φ termO
  rw [map_zero,map_terminalAt φ hO uO vO lO dO] at z
  apply certificate (φ hO) (φ uO) (φ vO) (φ lO) (φ dO) _ _ _ _ z
  · simpa only [map_mul,map_ofNat,map_one] using congrArg φ dO_mul
  · have f : φ.comp (Int.castRingHom O)=Int.castRingHom E := Subsingleton.elim ..
    rw [←f,←map_map,Polynomial.eval_map_apply,lrootO,map_zero]
  · simpa only [qO,map_pencilAt] using rootO.map φ
  · intro j
    have e := congrArg φ (auxO j)
    rw [map_zero,map_zEval φ (auxiliary j) (![lO,hO,uO,vO] : Fin 4→O)] at e
    have vectors : (fun i : Fin 4 => φ ((![lO,hO,uO,vO] : Fin 4→O) i)) =
        ![φ lO,φ hO,φ uO,φ vO] := by
      funext i
      fin_cases i <;> rfl
    rw [vectors] at e
    exact e

end RKCert.GoodPrimeDense
