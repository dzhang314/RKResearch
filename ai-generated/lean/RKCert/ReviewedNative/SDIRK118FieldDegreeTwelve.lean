module

public import RKCert.ReviewedNative.SDIRK118AlgebraicField
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Tactic.LinearCombination

@[expose] public section

noncomputable section

namespace RKResearch.Certified.PaidDefectBridge.SDIRK118.Subfield

open RKResearch ClaimPin ScalarBindings Polynomial
open RKResearch.Certified.DiagonalTwin (contractMatrix)
open RKResearch.Certified.Graded (mergeCoefficient)
open scoped Matrix

/-- A root of a stated monic polynomial, with its degree retained.
There is no assertion that this polynomial is minimal or irreducible. -/
def HasMonicRootOfDegree (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
    (x : L) (d : ℕ) : Prop :=
  ∃ P : Polynomial K, P.Monic ∧ P.natDegree = d ∧ aeval x P = 0

namespace HasMonicRootOfDegree

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem of_tail {x : L} {d : ℕ} {Q : Polynomial K} (hQ : Q.degree < d)
    (hx : aeval x ((X : Polynomial K)^d + Q) = 0) : HasMonicRootOfDegree K x d := by
  have hQ' : Q.degree < ((X : Polynomial K)^d).degree := by
    simpa only [degree_X_pow] using hQ
  refine ⟨(X : Polynomial K)^d + Q, monic_X_pow_add hQ, ?_, hx⟩
  calc
    _ = ((X : Polynomial K)^d).natDegree := natDegree_add_eq_left_of_degree_lt hQ'
    _ = d := natDegree_X_pow d

theorem isIntegral {x : L} {d : ℕ} (h : HasMonicRootOfDegree K x d) : IsIntegral K x := by
  obtain ⟨P,hP,_,hx⟩ := h
  exact ⟨P,hP,hx⟩

theorem minpoly_natDegree_le {x : L} {d : ℕ} (h : HasMonicRootOfDegree K x d) :
    (minpoly K x).natDegree ≤ d := by
  obtain ⟨P,hP,hd,hx⟩ := h
  calc
    (minpoly K x).natDegree ≤ P.natDegree :=
      Polynomial.natDegree_le_of_dvd (minpoly.dvd K x hx) hP.ne_zero
    _ = d := hd

theorem simple_finite_degree {x : L} {d : ℕ} (h : HasMonicRootOfDegree K x d) :
    FiniteDimensional K (IntermediateField.adjoin K ({x} : Set L)) ∧
      Module.finrank K (IntermediateField.adjoin K ({x} : Set L)) ≤ d := by
  have hx := h.isIntegral
  refine ⟨IntermediateField.adjoin.finiteDimensional hx, ?_⟩
  rw [IntermediateField.adjoin.finrank hx]
  exact h.minpoly_natDegree_le

end HasMonicRootOfDegree

/-- Same cubic as in Phase 2; the degree-three certificate is retained. -/
theorem seed_s_monicRoot {s : ℝ} (hs : s^3-9*s^2+18*s-6=0) :
    HasMonicRootOfDegree ℚ s 3 := by
  let Q : Polynomial ℚ := monomial 2 (-9) + monomial 1 18 + C (-6)
  refine HasMonicRootOfDegree.of_tail (Q := Q) ?_ ?_
  · refine (degree_lt_iff_coeff_zero _ 3).2 ?_
    intro n hn
    have h0 : n ≠ 0 := ne_of_gt ((show (0:ℕ) < 3 by decide).trans_le hn)
    have h1 : n ≠ 1 := ne_of_gt ((show (1:ℕ) < 3 by decide).trans_le hn)
    have h2 : n ≠ 2 := ne_of_gt ((show (2:ℕ) < 3 by decide).trans_le hn)
    simp [Q, coeff_add, coeff_C, Finsupp.single_apply, h0, h1, h2, h1.symm, h2.symm]
  · simp only [Q, map_add, aeval_X_pow, aeval_monomial, aeval_C, map_neg, map_ofNat, pow_one]
    linear_combination hs

private theorem quadratic_monicRoot (F : IntermediateField ℚ ℝ)
    {x a b : ℝ} (ha : a ∈ F) (hb : b ∈ F) (h : x^2+a*x+b=0) :
    HasMonicRootOfDegree F x 2 := by
  let aF : F := ⟨a,ha⟩
  let bF : F := ⟨b,hb⟩
  let Q : Polynomial F := monomial 1 aF + C bF
  refine HasMonicRootOfDegree.of_tail (Q := Q) ?_ ?_
  · refine (degree_lt_iff_coeff_zero _ 2).2 ?_
    intro n hn
    have h0 : n ≠ 0 := ne_of_gt ((show (0:ℕ) < 2 by decide).trans_le hn)
    have h1 : n ≠ 1 := ne_of_gt ((show (1:ℕ) < 2 by decide).trans_le hn)
    simp [Q, coeff_add, coeff_C, Finsupp.single_apply, h0, h1, h1.symm]
  · simp only [Q, map_add, aeval_X_pow, aeval_monomial, aeval_C,
      IntermediateField.algebraMap_apply, pow_one]
    change x^2+(a*x+b)=0
    simpa only [add_assoc] using h

theorem seed_t_monicRoot_over_single {s t : ℝ} (ht : qSeed s t=0) :
    HasMonicRootOfDegree (seedSingleField s) t 2 := by
  let F := seedSingleField s
  have hs : s ∈ F := mem_seedSingleField s
  have hb : -(s+3) ∈ F := F.neg_mem (F.add_mem hs (ofNat_mem F 3))
  apply quadratic_monicRoot F hb hs
  simpa only [qSeed, sub_eq_add_neg, neg_mul] using ht

theorem seed_c_monicRoot_over_pair (M : MonomialBasis) (hm : standardPowers M)
    {s t c : ℝ} (hc : quadraticAt M s t c=0) :
    HasMonicRootOfDegree (seedPairField s t) c 2 := by
  let F := seedPairField s t
  have hs : s ∈ F := seedPair_left s t
  have ht : t ∈ F := seedPair_right s t
  exact quadratic_monicRoot F (beta1_mem F M hm hs ht) (beta0_mem F M hm hs ht) hc

/-- Use the field arising by adjoining one new root, with its canonical
tower instances, before identifying it with a named ℚ-subfield. -/
private theorem extend_finite_degree (F : IntermediateField ℚ ℝ) {x : ℝ} {k d : ℕ}
    (hF : FiniteDimensional ℚ F ∧ Module.finrank ℚ F ≤ k)
    (hx : HasMonicRootOfDegree F x d) :
    FiniteDimensional ℚ ((IntermediateField.adjoin F ({x} : Set ℝ)).restrictScalars ℚ) ∧
      Module.finrank ℚ ((IntermediateField.adjoin F ({x} : Set ℝ)).restrictScalars ℚ) ≤ k*d := by
  let E₀ : IntermediateField F ℝ := IntermediateField.adjoin F ({x} : Set ℝ)
  let E : IntermediateField ℚ ℝ := E₀.restrictScalars ℚ
  have hE₀ := hx.simple_finite_degree
  letI : FiniteDimensional ℚ F := hF.1
  letI : FiniteDimensional F E := by
    change FiniteDimensional F E₀
    exact hE₀.1
  have hE : Module.finrank F E ≤ d := by
    change Module.finrank F E₀ ≤ d
    exact hE₀.2
  change FiniteDimensional ℚ E ∧ Module.finrank ℚ E ≤ k*d
  refine ⟨FiniteDimensional.trans ℚ F E, ?_⟩
  calc
    Module.finrank ℚ E = Module.finrank ℚ F * Module.finrank F E :=
      (Module.finrank_mul_finrank ℚ F E).symm
    _ ≤ k*d := Nat.mul_le_mul hF.2 hE

theorem seedPairField_restrict_tower (s t : ℝ) :
    (IntermediateField.adjoin (seedSingleField s) ({t} : Set ℝ)).restrictScalars ℚ =
      seedPairField s t := by
  unfold seedSingleField seedPairField
  rw [IntermediateField.adjoin_adjoin_left, Set.singleton_union]

theorem seedCoefficientField_restrict_tower (s t c : ℝ) :
    (IntermediateField.adjoin (seedPairField s t) ({c} : Set ℝ)).restrictScalars ℚ =
      seedCoefficientField s t c := by
  have hset : (({s,t} : Set ℝ) ∪ {c}) = {s,t,c} := by
    ext x
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, or_assoc]
  unfold seedPairField seedCoefficientField
  rw [IntermediateField.adjoin_adjoin_left, hset]

theorem seedSingleField_finite_degree {s : ℝ} (hs : s^3-9*s^2+18*s-6=0) :
    FiniteDimensional ℚ (seedSingleField s) ∧ Module.finrank ℚ (seedSingleField s) ≤ 3 :=
  (seed_s_monicRoot hs).simple_finite_degree

theorem seedPairField_finite_degree {s t : ℝ} (hs : s^3-9*s^2+18*s-6=0) (ht : qSeed s t=0) :
    FiniteDimensional ℚ (seedPairField s t) ∧ Module.finrank ℚ (seedPairField s t) ≤ 6 := by
  have H := extend_finite_degree (seedSingleField s) (seedSingleField_finite_degree hs)
    (seed_t_monicRoot_over_single ht)
  have eq := congrArg (fun E : IntermediateField ℚ ℝ =>
    FiniteDimensional ℚ E ∧ Module.finrank ℚ E ≤ 3*2) (seedPairField_restrict_tower s t)
  exact Eq.mp eq H

/-- A finite extension of degree at most twelve, not necessarily degree twelve. -/
theorem seedCoefficientField_finite_degree (M : MonomialBasis) (hm : standardPowers M)
    {s t c : ℝ} (seed : ExactScalarSeed M s t c) :
    FiniteDimensional ℚ (seedCoefficientField s t c) ∧
      Module.finrank ℚ (seedCoefficientField s t c) ≤ 12 := by
  have H := extend_finite_degree (seedPairField s t)
    (seedPairField_finite_degree seed.sRoot seed.tRoot)
    (seed_c_monicRoot_over_pair M hm seed.cRoot)
  have eq := congrArg (fun E : IntermediateField ℚ ℝ =>
    FiniteDimensional ℚ E ∧ Module.finrank ℚ E ≤ 6*2) (seedCoefficientField_restrict_tower s t c)
  exact Eq.mp eq H

/-- The same literal map-back statement from Phase 2, with a degree bound
and a genuine finite-dimensionality certificate for its coefficient field. -/
theorem literal_lift_finite_degree (M : MonomialBasis) (hm : standardPowers M)
    (e : (Fin 4 ⊕ Fin 8) ≃ Fin 12)
    {s t c : ℝ} (seed : ExactScalarSeed M s t c) (ho : LiteralStrictOrder8 M s t c e) :
    let F := seedCoefficientField s t c
    let g := geometry M s t c
    let A11 := contractMatrix (4 : Fin 12) (2 : Fin 11) (g.A.submatrix e.symm e.symm)
    let b11 := mergeCoefficient (4 : Fin 12) (2 : Fin 11) (g.b ∘ e.symm)
    FiniteDimensional ℚ F ∧ Module.finrank ℚ F ≤ 12 ∧
      ∃ (AF : Matrix (Fin 11) (Fin 11) F) (bF : Fin 11 → F) (γF : F),
        0 < γF ∧ AF.IsLowerTriangular ∧ (∀ i, AF i i=γF) ∧ HasOrder 8 AF bF ∧
        AF.map F.val.toRingHom=A11 ∧ F.val.toRingHom ∘ bF=b11 ∧ (γF : ℝ)=g.γ := by
  have hd := seedCoefficientField_finite_degree M hm seed
  have h := literal_lift_seedCoefficientField M hm e seed ho
  exact ⟨hd.1,hd.2,h.2⟩

def DegreeTwelveTarget : Prop :=
  ∃ F : IntermediateField ℚ ℝ, FiniteDimensional ℚ F ∧ Module.finrank ℚ F ≤ 12 ∧
    ∃ (A : Matrix (Fin 11) (Fin 11) F) (b : Fin 11 → F) (γ : F),
      0 < γ ∧ A.IsLowerTriangular ∧ (∀ i, A i i=γ) ∧ HasOrder 8 A b

theorem exists_degreeTwelve_of_real_producers (hcond : ConditionalTarget) (hex : ScalarExistenceTarget)
    (M : MonomialBasis) (hm : standardPowers M) (e : (Fin 4 ⊕ Fin 8) ≃ Fin 12)
    (he : orderedBlocks e) : DegreeTwelveTarget := by
  obtain ⟨s,t,c,seed⟩ := hex M hm
  obtain ⟨hF,hdeg,A,b,γ,hp,hL,hd,ho,_⟩ :=
    literal_lift_finite_degree M hm e seed (hcond M hm e he s t c seed)
  exact ⟨seedCoefficientField s t c,hF,hdeg,A,b,γ,hp,hL,hd,ho⟩

end RKResearch.Certified.PaidDefectBridge.SDIRK118.Subfield
