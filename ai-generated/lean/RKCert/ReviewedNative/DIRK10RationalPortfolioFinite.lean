module

public import RKCert.ReviewedNative.DIRK10RationalPortfolio
public import Mathlib.Data.Nat.Factorization.Induction
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.CharP.Defs

@[expose] public section

/-! Chinese remaindering of the two width-twelve witnesses. Every factor
uses a unit eleventh-bush witness, so the glued tableau does also. -/

namespace RKResearch.Certified.DIRK10RationalPortfolio
universe u

open RKResearch FiniteRootedTree
open scoped Matrix

variable {R S : Type*} [CommRing R] [CommRing S]

theorem paid_map (f : R →+* S) (h : Paid R) : Paid S := by
  obtain ⟨A,b,hl,ho,hu⟩ := h
  refine ⟨A.map f, f ∘ b, ?_, ho.map f, ?_⟩
  · intro i j hij
    change f (A i j) = 0
    rw [hl hij, map_zero]
  · unfold UnitBush at hu ⊢
    simpa only [map_sub,map_one,map_mul,map_natCast,RingHom.map_dotProduct,map_Φ] using
      hu.map f

theorem paid_product (h₁ : Paid R) (h₂ : Paid S) : Paid (R × S) := by
  obtain ⟨A₁,b₁,l₁,o₁,u₁⟩ := h₁
  obtain ⟨A₂,b₂,l₂,o₂,u₂⟩ := h₂
  let U : Matrix (Fin 12) (Fin 12) (R × S) := fun i j => (A₁ i j,A₂ i j)
  let b : Fin 12 → R × S := fun i => (b₁ i,b₂ i)
  have hAf : U.map (RingHom.fst R S) = A₁ := rfl
  have hAs : U.map (RingHom.snd R S) = A₂ := rfl
  have hbf : (RingHom.fst R S) ∘ b = b₁ := rfl
  have hbs : (RingHom.snd R S) ∘ b = b₂ := rfl
  refine ⟨U,b,?_,?_,?_⟩
  · intro i j hij
    exact Prod.ext (l₁ hij) (l₂ hij)
  · intro t ht
    apply Prod.ext
    · change (RingHom.fst R S) ((t.factorial:R×S)*(b ⬝ᵥ Φ t U)) = 1
      simpa only [map_mul,map_natCast,RingHom.map_dotProduct,map_Φ,hAf,hbf] using o₁ t ht
    · change (RingHom.snd R S) ((t.factorial:R×S)*(b ⬝ᵥ Φ t U)) = 1
      simpa only [map_mul,map_natCast,RingHom.map_dotProduct,map_Φ,hAs,hbs] using o₂ t ht
  · unfold UnitBush at u₁ u₂ ⊢
    apply Prod.isUnit_iff.mpr
    constructor
    · change IsUnit ((RingHom.fst R S) (((bushyTree 11).factorial:R×S)*(b ⬝ᵥ Φ (bushyTree 11) U)-1))
      simpa only [map_sub,map_one,map_mul,map_natCast,RingHom.map_dotProduct,map_Φ,hAf,hbf] using u₁
    · change IsUnit ((RingHom.snd R S) (((bushyTree 11).factorial:R×S)*(b ⬝ᵥ Φ (bushyTree 11) U)-1))
      simpa only [map_sub,map_one,map_mul,map_natCast,RingHom.map_dotProduct,map_Φ,hAs,hbs] using u₂

private theorem unit_of_zero_coprime {n m : ℕ} (hn : (n:R)=0)
    (hc : Nat.Coprime n m) : IsUnit (m:R) := by
  have h : IsCoprime (n:R) (m:R) := hc.cast
  rwa [hn, isCoprime_zero_left] at h

private theorem base_denominator_cast :
    (DIRK10RationalTwelve.D:R) = (Arithmetic.D₁:R) := by
  simp only [DIRK10RationalTwelve.D, Arithmetic.D₁, Int.cast_ofNat, Nat.cast_ofNat]

private theorem alternate_denominator_cast :
    (DIRK10RationalTwelveAlternateFlagReplay.denominator:R) = (Arithmetic.D₂:R) := by
  simp only [DIRK10RationalTwelveAlternateFlagReplay.denominator, Arithmetic.D₂,
    Int.cast_ofNat, Nat.cast_ofNat]

private def PaidAt (n : ℕ) : Prop :=
  ∀ (T : Type u) [CommRing T], (n:T)=0 → Nat.Coprime n 27216000 → Paid T

private theorem paid_annihilator (n : ℕ) : PaidAt.{u} n := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    intro T _ hzero hcop
    have hps := (Nat.coprime_pow_left_iff hk p 27216000).mp hcop
    by_cases hD : p ∣ Arithmetic.D₁
    · have hD₂ : ¬p ∣ 19891 * Arithmetic.D₂ := by
        intro hd₂
        exact (hp.coprime_iff_not_dvd.mp hps) (Arithmetic.denomCover ▸ Nat.dvd_gcd hD hd₂)
      have hc := (Nat.coprime_pow_left_iff hk p _).mpr (hp.coprime_iff_not_dvd.mpr hD₂)
      have hu := unit_of_zero_coprime hzero hc
      rw [Nat.cast_mul] at hu
      obtain ⟨hn,hD⟩ := IsUnit.mul_iff.mp hu
      exact paid_alternate (by rw [alternate_denominator_cast]; exact hD) hn
    · have hc := (Nat.coprime_pow_left_iff hk p _).mpr (hp.coprime_iff_not_dvd.mpr hD)
      exact paid_base (by rw [base_denominator_cast]; exact unit_of_zero_coprime hzero hc)
  | zero =>
    intro T _ _ hcop
    exact ((by decide +kernel : ¬Nat.Coprime 0 27216000) hcop).elim
  | one =>
    intro T _ hz _
    have hu := unit_of_zero_coprime hz (Nat.coprime_one_left Arithmetic.D₁)
    exact paid_base (by rw [base_denominator_cast]; exact hu)
  | coprime n₁ n₂ _ _ hcop ih₁ ih₂ =>
    intro T _ hzero hgood
    let I : Ideal T := Ideal.span {(n₁:T)}
    let J : Ideal T := Ideal.span {(n₂:T)}
    have hIJ : IsCoprime I J := (Ideal.isCoprime_span_singleton_iff _ _).mpr hcop.cast
    have heq : I*J = ⊥ := by
      simp only [I,J,Ideal.span_singleton_mul_span_singleton,←Nat.cast_mul,hzero,
        Ideal.span_singleton_zero]
    have hI : (n₁ : T ⧸ I)=0 := by
      rw [← map_natCast (Ideal.Quotient.mk I)]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    have hJ : (n₂ : T ⧸ J)=0 := by
      rw [← map_natCast (Ideal.Quotient.mk J)]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    have a := ih₁ (T ⧸ I) hI (hgood.of_dvd_left (dvd_mul_right n₁ n₂))
    have b := ih₂ (T ⧸ J) hJ (hgood.of_dvd_left (dvd_mul_left n₂ n₁))
    let e : T ≃+* (T ⧸ I) × (T ⧸ J) :=
      (RingEquiv.quotientBot T).symm.trans <|
        (Ideal.quotEquivOfEq heq.symm).trans (Ideal.quotientMulEquivQuotientProd I J hIJ)
    exact paid_map e.symm.toRingHom (paid_product a b)

private theorem coprime_of_char_and_unit (n : ℕ) [CharP R n] (hn : n≠0)
    (hu : IsUnit (27216000:R)) : Nat.Coprime n 27216000 := by
  unfold Nat.Coprime
  generalize hg : Nat.gcd n 27216000 = g
  have hgd : g ∣ 27216000 := hg ▸ Nat.gcd_dvd_right n 27216000
  have hgR : IsUnit (g:R) := isUnit_of_dvd_unit ((Nat.castRingHom R).map_dvd hgd) hu
  obtain ⟨m,hm⟩ := hg ▸ Nat.gcd_dvd_left n 27216000
  have hmul : (g:R)*(m:R)=0 := by
    rw [←Nat.cast_mul, ←hm, CharP.cast_eq_zero R n]
  have hmz := hgR.mul_right_eq_zero.mp hmul
  have hnm : n∣m := (CharP.cast_eq_zero_iff R n m).mp hmz
  have hmn : m∣n := ⟨g, by simpa [Nat.mul_comm] using hm⟩
  have heq : m=n := Nat.dvd_antisymm hmn hnm
  apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hn)
  simpa [heq] using hm.symm

theorem paid_finite_characteristic (n : ℕ) [CharP R n] (hn : n≠0)
    (h : IsUnit ((Nat.factorial 10:ℕ):R)) : Paid R :=
  paid_annihilator n R (CharP.cast_eq_zero R n) (coprime_of_char_and_unit n hn (smooth_unit h))

theorem exists_exact_finite_characteristic [Nontrivial R] (n : ℕ) [CharP R n] (hn : n≠0)
    (h : IsUnit ((Nat.factorial 10:ℕ):R)) :
    ∃ (A : Matrix (Fin 12) (Fin 12) R) (b : Fin 12 → R),
      A.IsLowerTriangular ∧ HasOrder 10 A b ∧ ¬HasOrder 11 A b := by
  obtain ⟨A,b,hL,ho,hu⟩ := paid_finite_characteristic n hn h
  exact ⟨A,b,hL,ho,not_order_eleven hu⟩

/-- Every field of characteristic zero or at least eleven admits a literal
portfolio witness of width twelve, with no minimality claim over that field. -/
theorem exists_exact_field (K : Type*) [Field K] (n : ℕ) [CharP K n] (h : n=0 ∨ 11≤n) :
    ∃ (A : Matrix (Fin 12) (Fin 12) K) (b : Fin 12 → K),
      A.IsLowerTriangular ∧ HasOrder 10 A b ∧ ¬ HasOrder 11 A b := by
  rcases h with rfl | hn
  · exact @DIRK10RationalTwelve.exists_exact_charZero K _ (CharP.charP_to_charZero K)
  · have hnz : n≠0 := by omega
    have hp := CharP.char_prime_of_ne_zero (R := K) hnz
    apply exists_exact_finite_characteristic n hnz
    apply isUnit_iff_ne_zero.mpr
    intro hzero
    have hdvd := (CharP.cast_eq_zero_iff K n (Nat.factorial 10)).mp hzero
    rw [show Nat.factorial 10 = 2^8*3^4*5^2*7 by decide +kernel] at hdvd
    rw [hp.dvd_mul, hp.dvd_mul, hp.dvd_mul] at hdvd
    rcases hdvd with ((h₂ | h₃) | h₅) | h₇
    · have hle := Nat.le_of_dvd (by decide : 0<2) (hp.dvd_of_dvd_pow h₂)
      omega
    · have hle := Nat.le_of_dvd (by decide : 0<3) (hp.dvd_of_dvd_pow h₃)
      omega
    · have hle := Nat.le_of_dvd (by decide : 0<5) (hp.dvd_of_dvd_pow h₅)
      omega
    · have hle := Nat.le_of_dvd (by decide : 0<7) h₇
      omega

end RKResearch.Certified.DIRK10RationalPortfolio
