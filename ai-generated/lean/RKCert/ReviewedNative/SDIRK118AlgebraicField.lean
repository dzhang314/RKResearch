module

public import RKCert.ReviewedNative.SDIRK118SubfieldDonor
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import RKResearch.OrderConditions

import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Tactic.LinearCombination

@[expose] public section

noncomputable section

namespace RKResearch.Certified.PaidDefectBridge.SDIRK118.Subfield

open RKResearch ClaimPin ScalarBindings Polynomial
open RKResearch.Certified.DiagonalTwin (contractMatrix)
open RKResearch.Certified.Graded (mergeCoefficient)
open scoped Matrix

/-- Generated inside ℝ, not abstract choices of number fields. -/
def seedSingleField (s : ℝ) : IntermediateField ℚ ℝ :=
  IntermediateField.adjoin ℚ ({s} : Set ℝ)

def seedPairField (s t : ℝ) : IntermediateField ℚ ℝ :=
  IntermediateField.adjoin ℚ ({s,t} : Set ℝ)

def seedCoefficientField (s t c : ℝ) : IntermediateField ℚ ℝ :=
  IntermediateField.adjoin ℚ ({s,t,c} : Set ℝ)

theorem mem_seedSingleField (s : ℝ) : s ∈ seedSingleField s :=
  IntermediateField.mem_adjoin_of_mem ℚ (show s ∈ ({s} : Set ℝ) from by simp)

theorem seedPair_left (s t : ℝ) : s ∈ seedPairField s t :=
  IntermediateField.mem_adjoin_of_mem ℚ (show s ∈ ({s,t} : Set ℝ) from by simp)

theorem seedPair_right (s t : ℝ) : t ∈ seedPairField s t :=
  IntermediateField.mem_adjoin_of_mem ℚ (show t ∈ ({s,t} : Set ℝ) from by simp)

theorem seedCoefficient_s (s t c : ℝ) : s ∈ seedCoefficientField s t c :=
  IntermediateField.mem_adjoin_of_mem ℚ (show s ∈ ({s,t,c} : Set ℝ) from by simp)

theorem seedCoefficient_t (s t c : ℝ) : t ∈ seedCoefficientField s t c :=
  IntermediateField.mem_adjoin_of_mem ℚ (show t ∈ ({s,t,c} : Set ℝ) from by simp)

theorem seedCoefficient_c (s t c : ℝ) : c ∈ seedCoefficientField s t c :=
  IntermediateField.mem_adjoin_of_mem ℚ (show c ∈ ({s,t,c} : Set ℝ) from by simp)

private theorem algebraic_adjoin {S : Set ℝ} (h : ∀ x ∈ S, IsAlgebraic ℚ x) :
    Algebra.IsAlgebraic ℚ (IntermediateField.adjoin ℚ S) := by
  apply IntermediateField.isAlgebraic_adjoin
  intro x hx
  exact (h x hx).isIntegral

theorem seed_s_isAlgebraic {s : ℝ} (hs : s^3-9*s^2+18*s-6=0) : IsAlgebraic ℚ s := by
  let P : Polynomial ℚ := X^3 + (monomial 2 (-9) + monomial 1 18 + C (-6))
  have hP : P.Monic := by
    apply monic_X_pow_add
    refine (degree_lt_iff_coeff_zero _ 3).2 ?_
    intro n hn
    have h0 : n ≠ 0 := ne_of_gt ((show (0:ℕ) < 3 by decide).trans_le hn)
    have h1 : n ≠ 1 := ne_of_gt ((show (1:ℕ) < 3 by decide).trans_le hn)
    have h2 : n ≠ 2 := ne_of_gt ((show (2:ℕ) < 3 by decide).trans_le hn)
    simp [coeff_add, coeff_C, Finsupp.single_apply, h0, h1, h2, h1.symm, h2.symm]
  refine ⟨P, hP.ne_zero, ?_⟩
  simp only [P, map_add, aeval_X_pow, aeval_monomial, aeval_C, map_neg, map_ofNat, pow_one]
  linear_combination hs

/-- A monic quadratic in the actual smaller intermediate field. -/
private theorem isAlgebraic_of_quadratic (F : IntermediateField ℚ ℝ)
    {x a b : ℝ} (ha : a ∈ F) (hb : b ∈ F) (h : x^2+a*x+b=0) : IsAlgebraic F x := by
  let aF : F := ⟨a,ha⟩
  let bF : F := ⟨b,hb⟩
  let P : Polynomial F := X^2 + (monomial 1 aF + C bF)
  have hP : P.Monic := by
    apply monic_X_pow_add
    refine (degree_lt_iff_coeff_zero _ 2).2 ?_
    intro n hn
    have h0 : n ≠ 0 := ne_of_gt ((show (0:ℕ) < 2 by decide).trans_le hn)
    have h1 : n ≠ 1 := ne_of_gt ((show (1:ℕ) < 2 by decide).trans_le hn)
    simp [coeff_add, coeff_C, Finsupp.single_apply, h0, h1, h1.symm]
  refine ⟨P, hP.ne_zero, ?_⟩
  simp only [P, map_add, aeval_X_pow, aeval_monomial, aeval_C, IntermediateField.algebraMap_apply,
    pow_one]
  change x^2+(a*x+b)=0
  simpa only [add_assoc] using h

theorem seed_t_isAlgebraic_over_single {s t : ℝ} (ht : qSeed s t=0) :
    IsAlgebraic (seedSingleField s) t := by
  let F := seedSingleField s
  have hs : s ∈ F := mem_seedSingleField s
  have hb : -(s+3) ∈ F := F.neg_mem (F.add_mem hs (ofNat_mem F 3))
  apply isAlgebraic_of_quadratic F hb hs
  simpa only [qSeed, sub_eq_add_neg, neg_mul] using ht

theorem seed_t_isAlgebraic {s t : ℝ} (hs : IsAlgebraic ℚ s) (ht : qSeed s t=0) :
    IsAlgebraic ℚ t := by
  letI : Algebra.IsAlgebraic ℚ (seedSingleField s) := by
    apply algebraic_adjoin
    intro x hx
    simpa only [(Set.mem_singleton_iff.mp hx)] using hs
  exact (seed_t_isAlgebraic_over_single ht).restrictScalars ℚ

theorem seedPairField_isAlgebraic {s t : ℝ} (hs : IsAlgebraic ℚ s) (ht : IsAlgebraic ℚ t) :
    Algebra.IsAlgebraic ℚ (seedPairField s t) := by
  apply algebraic_adjoin
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact hs
  · exact ht

theorem seed_c_isAlgebraic_over_pair (M : MonomialBasis) (hm : standardPowers M)
    {s t c : ℝ} (hc : quadraticAt M s t c=0) : IsAlgebraic (seedPairField s t) c := by
  let F := seedPairField s t
  have hs : s ∈ F := seedPair_left s t
  have ht : t ∈ F := seedPair_right s t
  exact isAlgebraic_of_quadratic F (beta1_mem F M hm hs ht) (beta0_mem F M hm hs ht) hc

theorem seed_c_isAlgebraic (M : MonomialBasis) (hm : standardPowers M)
    {s t c : ℝ} (hs : IsAlgebraic ℚ s) (ht : IsAlgebraic ℚ t)
    (hc : quadraticAt M s t c=0) : IsAlgebraic ℚ c := by
  letI := seedPairField_isAlgebraic hs ht
  exact (seed_c_isAlgebraic_over_pair M hm hc).restrictScalars ℚ

theorem exact_seed_isAlgebraic (M : MonomialBasis) (hm : standardPowers M)
    {s t c : ℝ} (hsd : ExactScalarSeed M s t c) :
    IsAlgebraic ℚ s ∧ IsAlgebraic ℚ t ∧ IsAlgebraic ℚ c := by
  have hs := seed_s_isAlgebraic hsd.sRoot
  have ht := seed_t_isAlgebraic hs hsd.tRoot
  exact ⟨hs,ht,seed_c_isAlgebraic M hm hs ht hsd.cRoot⟩

theorem seedCoefficientField_isAlgebraic (M : MonomialBasis) (hm : standardPowers M)
    {s t c : ℝ} (hsd : ExactScalarSeed M s t c) :
    Algebra.IsAlgebraic ℚ (seedCoefficientField s t c) := by
  obtain ⟨hs, ht, hc⟩ := exact_seed_isAlgebraic M hm hsd
  apply algebraic_adjoin
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact hs
  · exact ht
  · exact hc

theorem literal_coefficients_isAlgebraic (M : MonomialBasis) (hm : standardPowers M)
    (e : (Fin 4 ⊕ Fin 8) ≃ Fin 12)
    {s t c : ℝ} (hsd : ExactScalarSeed M s t c) :
    let g := geometry M s t c
    let A11 := contractMatrix (4 : Fin 12) (2 : Fin 11) (g.A.submatrix e.symm e.symm)
    let b11 := mergeCoefficient (4 : Fin 12) (2 : Fin 11) (g.b ∘ e.symm)
    (∀ i j, IsAlgebraic ℚ (A11 i j)) ∧ (∀ i, IsAlgebraic ℚ (b11 i)) ∧ IsAlgebraic ℚ g.γ := by
  let F := seedCoefficientField s t c
  letI : Algebra.IsAlgebraic ℚ F := seedCoefficientField_isAlgebraic M hm hsd
  obtain ⟨hA,hb,hγ⟩ := literal_coefficients_mem F M hm e
    (seedCoefficient_s s t c) (seedCoefficient_t s t c) (seedCoefficient_c s t c)
  have hmem {x : ℝ} (hx : x ∈ F) : IsAlgebraic ℚ x :=
    (IntermediateField.isAlgebraic_iff (S := F) (x := ⟨x,hx⟩)).1
      (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (A := F) ⟨x,hx⟩)
  exact ⟨fun i j => hmem (hA i j), fun i => hmem (hb i), hmem hγ⟩

section Lift

variable (F : IntermediateField ℚ ℝ)

def liftMatrix {ι κ : Type*} {A : Matrix ι κ ℝ} (hA : MatIn F A) : Matrix ι κ F :=
  fun i j => ⟨A i j,hA i j⟩

def liftVector {ι : Type*} {b : ι → ℝ} (hb : VecIn F b) : ι → F :=
  fun i => ⟨b i,hb i⟩

theorem hasOrder_lift {ι : Type*} [Fintype ι] {p : ℕ}
    {A : Matrix ι ι ℝ} {b : ι → ℝ} (hA : MatIn F A) (hb : VecIn F b)
    (ho : HasOrder p A b) : HasOrder p (liftMatrix F hA) (liftVector F hb) := by
  apply (RKResearch.hasOrder_map_iff (p := p) (A := liftMatrix F hA)
    (b := liftVector F hb) (f := F.val.toRingHom) F.val.injective).1
  exact ho

theorem lift_strict_hasOrder {n p : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {b : Fin n → ℝ}
    {γ : ℝ} (hA : MatIn F A) (hb : VecIn F b) (hγ : γ ∈ F)
    (ho : 0 < γ ∧ A.IsLowerTriangular ∧ (∀ i, A i i = γ) ∧ HasOrder p A b) :
    ∃ (AF : Matrix (Fin n) (Fin n) F) (bF : Fin n → F) (γF : F),
      0 < γF ∧ AF.IsLowerTriangular ∧ (∀ i, AF i i = γF) ∧ HasOrder p AF bF ∧
      AF.map F.val.toRingHom = A ∧ F.val.toRingHom ∘ bF = b ∧ (γF : ℝ) = γ := by
  obtain ⟨hp,hL,hd,hOrder⟩ := ho
  refine ⟨liftMatrix F hA, liftVector F hb, ⟨γ,hγ⟩, ?_, ?_, ?_,
    hasOrder_lift F hA hb hOrder, rfl, rfl, rfl⟩
  · exact hp
  · intro i j hij
    apply Subtype.ext
    exact hL hij
  · intro i
    exact Subtype.ext (hd i)

end Lift

/-- For the very same s,t,c and retained tableau, all three returned field
coefficients map back entrywise to the real witness. -/
theorem literal_lift_seedCoefficientField (M : MonomialBasis) (hm : standardPowers M)
    (e : (Fin 4 ⊕ Fin 8) ≃ Fin 12)
    {s t c : ℝ} (hsd : ExactScalarSeed M s t c) (ho : LiteralStrictOrder8 M s t c e) :
    let F := seedCoefficientField s t c
    let g := geometry M s t c
    let A11 := contractMatrix (4 : Fin 12) (2 : Fin 11) (g.A.submatrix e.symm e.symm)
    let b11 := mergeCoefficient (4 : Fin 12) (2 : Fin 11) (g.b ∘ e.symm)
    Algebra.IsAlgebraic ℚ F ∧
      ∃ (AF : Matrix (Fin 11) (Fin 11) F) (bF : Fin 11 → F) (γF : F),
        0 < γF ∧ AF.IsLowerTriangular ∧ (∀ i, AF i i = γF) ∧ HasOrder 8 AF bF ∧
        AF.map F.val.toRingHom = A11 ∧ F.val.toRingHom ∘ bF = b11 ∧ (γF : ℝ) = g.γ := by
  let F := seedCoefficientField s t c
  obtain ⟨hA,hb,hγ⟩ := literal_coefficients_mem F M hm e
    (seedCoefficient_s s t c) (seedCoefficient_t s t c) (seedCoefficient_c s t c)
  exact ⟨seedCoefficientField_isAlgebraic M hm hsd, lift_strict_hasOrder F hA hb hγ ho⟩

def CommonAlgebraicTarget : Prop :=
  ∃ F : IntermediateField ℚ ℝ, Algebra.IsAlgebraic ℚ F ∧
    ∃ (A : Matrix (Fin 11) (Fin 11) F) (b : Fin 11 → F) (γ : F),
      0 < γ ∧ A.IsLowerTriangular ∧ (∀ i, A i i = γ) ∧ HasOrder 8 A b

theorem exists_algebraic_of_real_producers (hcond : ConditionalTarget) (hex : ScalarExistenceTarget)
    (M : MonomialBasis) (hm : standardPowers M) (e : (Fin 4 ⊕ Fin 8) ≃ Fin 12)
    (he : orderedBlocks e) : CommonAlgebraicTarget := by
  obtain ⟨s,t,c,hsd⟩ := hex M hm
  obtain ⟨hF, A, b, γ, hp, hL, hd, ho, _⟩ :=
    literal_lift_seedCoefficientField M hm e hsd (hcond M hm e he s t c hsd)
  exact ⟨seedCoefficientField s t c, hF, A, b, γ, hp, hL, hd, ho⟩

end RKResearch.Certified.PaidDefectBridge.SDIRK118.Subfield
