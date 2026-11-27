module
public import RKCert.Research.SDIRKSevenStageOrderSixRing
public import RKCert.Research.SDIRKSixExceptionalSupport
public import RKCert.ReviewedNative.SDIRKSixChar11and17
public import RKCert.ReviewedNative.SDIRKSix163
public import RKCert.Research.SDIRKSix263
public import RKCert.Research.SDIRKSix457
public import RKCert.Research.SDIRKSix126963077
public import RKCert.Research.SDIRKSix3533Quadratic

public section

/-! # Matched order-six strict SDIRK endpoints over every field

The minimum is six in the explicitly listed coefficient fields and
seven in every other field where the paid factorial is nonzero.
No tableau exists if the paid factorial is zero. Only in characteristic
3533 does the answer depend on more than characteristic.
-/

namespace RKResearch
open Certified
open scoped Matrix

/-- At least classical order six at the literal physical stage count.
A common **unit** diagonal provides the strict notion over rings and
reduces to a nonzero common diagonal over coefficient fields. -/
@[expose] def HasStrictSDIRKOrderSix (R : Type*) [CommRing R] (s : ℕ) : Prop :=
  ∃ (A : Matrix (Fin s) (Fin s) R) (b : Fin s → R) (γ : R),
    A.IsLowerTriangular ∧ (∀ i, A i i = γ) ∧ IsUnit γ ∧ HasOrder 6 A b

namespace HasStrictSDIRKOrderSix

variable {R S : Type*} [CommRing R] [CommRing S] {s : ℕ}

theorem map (h : HasStrictSDIRKOrderSix R s) (f : R →+* S) :
    HasStrictSDIRKOrderSix S s := by
  obtain ⟨A,b,γ,ht,hγ,hu,ho⟩ := h
  exact ⟨A.map f, f ∘ b, f γ, ht.map f,
    fun i => congrArg f (hγ i), hu.map f, ho.map f⟩

theorem map_zmod {q : ℕ} (h : HasStrictSDIRKOrderSix (ZMod q) s)
    (hq : (q : R) = 0) : HasStrictSDIRKOrderSix R s :=
  h.map (ZMod.castHom (ringChar.dvd hq) R)

theorem factorial_unit (h : HasStrictSDIRKOrderSix R s) : IsUnit (720 : R) := by
  obtain ⟨_,_,_,_,_,_,ho⟩ := h
  exact ho.sixFactorial_isUnit

theorem seven [Nontrivial R] (h : IsUnit (720 : R)) : HasStrictSDIRKOrderSix R 7 := by
  obtain ⟨A,b,γ,ht,hγ,hu,_,ho,_⟩ := SDIRKSevenStageOrderSixRing.exists_exact h
  exact ⟨A,b,γ,ht,hγ,hu,ho⟩

/-- The existing quadratic lower bound specializes to six stages. -/
theorem six_le [Nontrivial R] (h : HasStrictSDIRKOrderSix R s) : 6 ≤ s := by
  obtain ⟨A,b,γ,ht,hγ,hu,ho⟩ := h
  exact ho.nonsingular_stageFloor ht (fun i => by rw [hγ i]; exact hu) (by decide)

theorem mod187 : HasStrictSDIRKOrderSix (ZMod 187) 6 :=
  ⟨SDIRKSixChar11and17.A, SDIRKSixChar11and17.b, SDIRKSixChar11and17.gamma,
    SDIRKSixChar11and17.lowerTriangular, SDIRKSixChar11and17.diagonal,
    SDIRKSixChar11and17.gamma_unit, SDIRKSixChar11and17.order_six⟩

theorem mod163 : HasStrictSDIRKOrderSix (ZMod 163) 6 :=
  ⟨SDIRKSix163.A, SDIRKSix163.b, SDIRKSix163.gamma,
    SDIRKSix163.lowerTriangular, SDIRKSix163.diagonal,
    IsUnit.of_mul_eq_one (39 : ZMod 163) (by decide +kernel), SDIRKSix163.order_six⟩

theorem mod263 : HasStrictSDIRKOrderSix (ZMod 263) 6 :=
  ⟨SDIRKSix263.A, SDIRKSix263.b, SDIRKSix263.gamma,
    SDIRKSix263.lowerTriangular, SDIRKSix263.diagonal,
    IsUnit.of_mul_eq_one (189 : ZMod 263) (by decide +kernel), SDIRKSix263.order_six⟩

theorem mod457 : HasStrictSDIRKOrderSix (ZMod 457) 6 :=
  ⟨SDIRKSix457.A, SDIRKSix457.b, SDIRKSix457.gamma,
    SDIRKSix457.lowerTriangular, SDIRKSix457.diagonal,
    IsUnit.of_mul_eq_one (187 : ZMod 457) (by decide +kernel), SDIRKSix457.order_six⟩

theorem mod126963077 : HasStrictSDIRKOrderSix (ZMod 126963077) 6 :=
  ⟨SDIRKSix126963077.A, SDIRKSix126963077.b, SDIRKSix126963077.gamma,
    SDIRKSix126963077.lowerTriangular, SDIRKSix126963077.diagonal,
    IsUnit.of_mul_eq_one (118528251 : ZMod 126963077) (by decide +kernel),
    SDIRKSix126963077.order_six⟩

theorem quadratic3533 : HasStrictSDIRKOrderSix SDIRKSix3533Quadratic.E 6 :=
  ⟨SDIRKSix3533Quadratic.A, SDIRKSix3533Quadratic.b, SDIRKSix3533Quadratic.gamma,
    SDIRKSix3533Quadratic.lowerTriangular, SDIRKSix3533Quadratic.diagonal,
    IsUnit.of_mul_eq_one (⟨1645, 0⟩ : SDIRKSix3533Quadratic.E) (by decide +kernel),
    SDIRKSix3533Quadratic.order_six⟩

end HasStrictSDIRKOrderSix

/-- A strict order-six method exists at any stage count only when
the factorial is a unit, and seven stages always suffice then. -/
theorem exists_strictSDIRKOrderSix_iff_factorial_unit {R : Type*} [CommRing R] [Nontrivial R] :
    (∃ s, HasStrictSDIRKOrderSix R s) ↔ IsUnit (720 : R) :=
  ⟨fun ⟨_,h⟩ => h.factorial_unit, fun h => ⟨7, HasStrictSDIRKOrderSix.seven h⟩⟩

/-- Each vanishing prime numeral in a field specifies its exact
characteristic. The last branch is the only extension-sensitive one. -/
@[expose] def SDIRKSixFieldAllowsSix (K : Type*) [Field K] : Prop :=
  (11 : K) = 0 ∨ (17 : K) = 0 ∨ (163 : K) = 0 ∨ (263 : K) = 0 ∨
    (457 : K) = 0 ∨ ((3533 : K) = 0 ∧ ∃ x : K, x^2 = 2077) ∨
    (126963077 : K) = 0

variable {K : Type*} [Field K]

theorem has_strictSDIRKOrderSix_six_iff :
    HasStrictSDIRKOrderSix K 6 ↔ SDIRKSixFieldAllowsSix K := by
  constructor
  · rintro ⟨A,b,γ,ht,hγ,hu,ho⟩
    have hz : (sixStageSupport : K) = 0 := by
      by_contra hn
      have h7 := ho.common_diagonal_order_six_stages_off_exceptional_support ht hγ
        (Or.inr (fun hh => hn (isNilpotent_iff_eq_zero.mp hh)))
      omega
    simp only [sixStageSupport_eq, Nat.cast_mul, Nat.cast_ofNat, mul_eq_zero, or_assoc] at hz
    rw [SDIRKSixFieldAllowsSix]
    rcases hz with h11|h17|h163|h263|h457|h3533|h126963077
    · exact Or.inl h11
    · exact Or.inr (Or.inl h17)
    · exact Or.inr (Or.inr (Or.inl h163))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h263)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h457))))
    · have hsq : ∃ x : K, x^2 = 2077 := by
        by_contra hns
        let : CharP K 3533 :=
          (CharP.charP_iff_prime_eq_zero SDIRKSix3533Quadratic.prime.out).mpr h3533
        have h7 := Graded.SDIRKSix.seven_le_of_strict_order_six_char3533_of_nonsquare
          ho ht hγ hu.ne_zero hns
        omega
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h3533,hsq⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h126963077)))))
  · intro h
    rw [SDIRKSixFieldAllowsSix] at h
    rcases h with h11|h17|h163|h263|h457|h3533|h126963077
    · exact HasStrictSDIRKOrderSix.mod187.map_zmod
        (by simp only [Nat.cast_ofNat]; rw [show (187 : K) = 11 * 17 by norm_num, h11, zero_mul])
    · exact HasStrictSDIRKOrderSix.mod187.map_zmod
        (by simp only [Nat.cast_ofNat]; rw [show (187 : K) = 11 * 17 by norm_num, h17, mul_zero])
    · exact HasStrictSDIRKOrderSix.mod163.map_zmod (by simpa only [Nat.cast_ofNat] using h163)
    · exact HasStrictSDIRKOrderSix.mod263.map_zmod (by simpa only [Nat.cast_ofNat] using h263)
    · exact HasStrictSDIRKOrderSix.mod457.map_zmod (by simpa only [Nat.cast_ofNat] using h457)
    · obtain ⟨hch, hsq⟩ := h3533
      let : CharP K 3533 :=
        (CharP.charP_iff_prime_eq_zero SDIRKSix3533Quadratic.prime.out).mpr hch
      obtain ⟨A,b,γ,ht,hγ,hn,ho,-⟩ := SDIRKSix3533Quadratic.exists_exact_of_sqrt hsq
      exact ⟨A,b,γ,ht,hγ,isUnit_iff_ne_zero.mpr hn,ho⟩
    · exact HasStrictSDIRKOrderSix.mod126963077.map_zmod
        (by simpa only [Nat.cast_ofNat] using h126963077)

private theorem seven_le_off_field_list {s : ℕ} (hn : ¬ SDIRKSixFieldAllowsSix K)
    (h : HasStrictSDIRKOrderSix K s) : 7 ≤ s := by
  have hf := h.six_le
  by_contra h7
  have hs : s = 6 := by omega
  exact hn (has_strictSDIRKOrderSix_six_iff.mp (hs ▸ h))

/-- Complete stage-minimum classification over any field, with neither
an ordering nor a characteristic-zero hypothesis. If 720 vanishes
neither alternative holds, and no strict order-six tableau exists. -/
theorem strictSDIRKOrderSix_minimum_field_iff (n : ℕ) :
    IsLeast {s : ℕ | HasStrictSDIRKOrderSix K s} n ↔
      (n = 6 ∧ SDIRKSixFieldAllowsSix K) ∨
      (n = 7 ∧ IsUnit (720 : K) ∧ ¬ SDIRKSixFieldAllowsSix K) := by
  constructor
  · intro h
    have hn : HasStrictSDIRKOrderSix K n := h.1
    by_cases hf : SDIRKSixFieldAllowsSix K
    · have h6 : HasStrictSDIRKOrderSix K 6 := has_strictSDIRKOrderSix_six_iff.mpr hf
      exact Or.inl ⟨le_antisymm (h.2 h6) hn.six_le, hf⟩
    · have h7 : HasStrictSDIRKOrderSix K 7 := HasStrictSDIRKOrderSix.seven hn.factorial_unit
      exact Or.inr ⟨le_antisymm (h.2 h7) (seven_le_off_field_list hf hn), hn.factorial_unit, hf⟩
  · rintro (⟨rfl,hf⟩|⟨rfl,hfac,hf⟩)
    · exact ⟨has_strictSDIRKOrderSix_six_iff.mpr hf, fun _ h => HasStrictSDIRKOrderSix.six_le h⟩
    · exact ⟨HasStrictSDIRKOrderSix.seven hfac, fun _ h => seven_le_off_field_list hf h⟩

end RKResearch
