module
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.NormNum

@[expose] public section
/-! # Good-prime reduction for integral divisor-moment obstructions
Only coefficients of a monic divisor of an integer monic polynomial, and a
root of another such polynomial, are reduced. A proposed RK tableau over a
characteristic-zero field is never reduced modulo a prime.
-/
namespace RKCert.FixedFactor
open Polynomial
universe u

/-- The integer form of the moment J(xP)(w) for P of degree at most D.
Choose L divisible by 2,…,D+2 for comparison with the characteristic-zero integral. -/
def moment {R : Type*} [CommSemiring R] (L D : ℕ) (P : R[X]) (w : R) : R :=
  ∑i∈Finset.range (D+1), (L/(i+2):ℕ)*P.coeff i*w^(i+2)

theorem map_moment {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S)
    (L D : ℕ) (P : R[X]) (w : R) :
    f (moment L D P w)=moment L D (P.map f) (f w) := by simp [moment]

/-- A prime-field obstruction, valid after any field extension, lifts to
every characteristic-zero field. Both test polynomials really are monic. -/
theorem good_prime {K : Type u} [Field K] [CharZero K] (p : ℕ) [Fact p.Prime]
    (F H : ℤ[X]) (hF : F.Monic) (hH : H.Monic) (L D : ℕ)
    (certificate : ∀ {E : Type u} [Field E] [CharP E p] (P : E[X]) (w : E),
      P.Monic → P∣F.map (Int.castRingHom E) → P.natDegree≤D →
      (H.map (Int.castRingHom E)).eval w=0 → moment L D P w≠0)
    (P : K[X]) (w : K) (hm : P.Monic) (hd : P∣F.map (Int.castRingHom K))
    (hdeg : P.natDegree≤D) (hw : (H.map (Int.castRingHom K)).eval w=0) :
    moment L D P w ≠ 0 := by
  classical
  intro hz
  let O := integralClosure ℤ K
  let ι : O →+* K := (integralClosure ℤ K).val.toRingHom
  have hi : Function.Injective ι := Subtype.coe_injective
  have iint : ι.comp (Int.castRingHom O)=Int.castRingHom K := Subsingleton.elim ..
  have lift (Q : K[X]) (qm : Q.Monic) (qd : Q ∣ F.map (Int.castRingHom K)) :
      ∃Q' : O[X], Q'.map ι=Q :=
    Polynomial.mem_lifts Q |>.mp (integralClosure.mem_lifts_of_monic_of_dvd_map K hF qm qd)
  obtain ⟨P',p'⟩:=lift P hm hd
  obtain ⟨T,ht⟩:=hd
  have tm : T.Monic := hm.of_mul_monic_left (ht ▸ hF.map (Int.castRingHom K))
  obtain ⟨T',t'⟩:=lift T tm (ht ▸ dvd_mul_left T P)
  have hm' : P'.Monic := hi.monic_map_iff.mpr (p' ▸ hm)
  have fact : F.map (Int.castRingHom O)=P'*T' := by
    apply Polynomial.map_injective ι hi
    rw [map_map,iint,Polynomial.map_mul,p',t',ht]
  have wh : IsIntegral ℤ w := ⟨H,hH,by rw [eval₂_eq_eval_map,algebraMap_int_eq]; exact hw⟩
  let w' : O := ⟨w,wh⟩
  have root : (H.map (Int.castRingHom O)).eval w'=0 := by
    apply hi
    rw [map_zero,←Polynomial.eval_map_apply,map_map,iint]
    exact hw
  have zero : moment L D P' w'=0 := by
    apply hi
    rw [map_zero,map_moment,p']
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
  have φint : φ.comp (Int.castRingHom O)=Int.castRingHom E := Subsingleton.elim ..
  apply certificate (P'.map φ) (φ w') (hm'.map φ)
  · have q:=congrArg (Polynomial.map φ) fact
    rw [map_map,φint,Polynomial.map_mul] at q
    exact ⟨_,q⟩
  · have e : P'.natDegree=P.natDegree := by rw [←p',natDegree_map_eq_of_injective hi]
    exact (natDegree_map_le ..).trans (e ▸ hdeg)
  · rw [←φint,←map_map,Polynomial.eval_map_apply,root,map_zero]
  · rw [←map_moment,zero,map_zero]

end RKCert.FixedFactor
