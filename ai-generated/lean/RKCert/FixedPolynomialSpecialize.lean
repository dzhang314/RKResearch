module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Ideal.Int
public import Mathlib.RingTheory.Polynomial.IntegralNormalization
public import Mathlib.RingTheory.Localization.FractionRing

@[expose] public section

/-! # Sound reduction of fixed integral root certificates
The ambient characteristic-zero field is never reduced. Only the integral
scaled roots are sent through the integral closure and a lying-over prime.
Any polynomial equations in those roots are preserved together, in a
field extension of the *fixed* prime field. Inequalities are not transferred. -/
namespace RKCert.FixedPolynomial
open MvPolynomial
universe u₁ u₂

structure Specialization (p : ℕ) {ι : Type u₁} {K : Type u₂} [Field K] (a : ι → K) where
  carrier : Type u₂
  [carrierField : Field carrier]
  embed : ZMod p →+* carrier
  image : ι → carrier
  preserves : ∀ F : MvPolynomial ι ℤ, F.eval₂ (Int.castRingHom K) a=0 →
    F.eval₂ (Int.castRingHom carrier) image=0

attribute [instance] Specialization.carrierField

theorem scaled_root_integral {K : Type u₂} [Field K] [CharZero K] (D : Polynomial ℤ) (hD : D≠0)
    {x : K} (hx : Polynomial.eval₂ (Int.castRingHom K) x D=0) :
    IsIntegral ℤ ((D.leadingCoeff:K)*x) := by
  refine ⟨D.integralNormalization,Polynomial.monic_integralNormalization hD,?_⟩
  change Polynomial.eval₂ (Int.castRingHom K) ((D.leadingCoeff:K)*x) D.integralNormalization=0
  exact Polynomial.integralNormalization_eval₂_eq_zero (Int.castRingHom K) hx
    (fun z hz => (Int.cast_injective (α:=K)) (by change (z:K)=0 at hz; simpa only [Int.cast_zero] using hz))

/-- Lying over for the genuine ring of integral elements, followed by the
fraction field of its integral-domain residue. Any integer polynomial in any
of the supplied algebraic integers may be used as a certificate equation. -/
theorem exists_specialization (p : ℕ) [hP : Fact p.Prime]
    {ι : Type u₁} {K : Type u₂} [Field K] [CharZero K] (a : ι → K)
    (ha : ∀ i, IsIntegral ℤ (a i)) : Nonempty (Specialization p a) := by
  let S := integralClosure ℤ K
  let P : Ideal ℤ := Ideal.span ({(p:ℤ)} : Set ℤ)
  have : P.IsMaximal := Int.ideal_span_isMaximal_of_prime p
  have inj : Function.Injective (algebraMap ℤ S) := by
    intro x y h
    apply (Int.cast_injective (α:=K))
    exact congrArg (fun a : S => (a:K)) h
  obtain ⟨Q,hQ,hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain
    (S:=S) P (by rw [(RingHom.injective_iff_ker_eq_bot _).mp inj]; exact bot_le)
  have : Q.IsPrime := hQ
  let L := FractionRing (S ⧸ Q)
  let ρ : S →+* L := (algebraMap (S ⧸ Q) L).comp (Ideal.Quotient.mk Q)
  have hpn : ((p:ℕ):L)=0 := by
    have hpz : (p:ℤ)∈P := Ideal.subset_span (Set.mem_singleton _)
    rw [←hQP] at hpz
    have hQp : (algebraMap ℤ S) (p:ℤ)∈Q := hpz
    have hz : Ideal.Quotient.mk Q ((algebraMap ℤ S) (p:ℤ))=0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hQp
    have he := congrArg (algebraMap (S ⧸ Q) L) hz
    simpa using he
  have : CharP L p := (CharP.charP_iff_prime_eq_zero hP.out).mpr hpn
  let aS : ι → S := fun i => ⟨a i,ha i⟩
  let aL : ι → L := fun i => ρ (aS i)
  refine ⟨{carrier := L,embed := ZMod.castHom (dvd_refl p) L, image := aL,preserves := ?_}⟩
  intro F h
  let incl : S →+* K := S.val.toRingHom
  have he (T : Type u₂) [CommRing T] (f : S →+* T) :
      f.comp (Int.castRingHom S)=Int.castRingHom T := by ext j; simp
  have h0 : F.eval₂ (Int.castRingHom S) aS=0 := by
    have hi : Function.Injective incl := Subtype.val_injective
    apply hi
    rw [map_zero,MvPolynomial.hom_eval₂,he K]
    exact h
  have hr := congrArg ρ h0
  rw [map_zero,MvPolynomial.hom_eval₂,he L] at hr
  exact hr

end RKCert.FixedPolynomial
