module

public import RKCert.ReviewedNative.NodalPaidHankel
public import Mathlib.LinearAlgebra.Dual.Lemmas

@[expose] public section

/-! # The half-degree corank bound for factored paid masks

Pair the two multiplication images in a rectangular ordinary clock
band. The smaller side is detected by its own paid square. Its image
in the larger side's dual then spends exactly its dimension from the
annihilator budget. No orthogonal-polynomial recurrence or extension
of the coefficient field is needed for the physical split mask.
-/

namespace RKResearch.Certified.Graded

open Module Polynomial
open scoped BigOperators Matrix Polynomial

noncomputable section

variable {K : Type*} [Field K]

section Pairing

variable {X Y V W : Type*}
variable [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
variable [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
variable [FiniteDimensional K V]

/-- A kernel sent injectively into a paired annihilator spends the
codimension of the independently embedded tests. -/
theorem finrank_ker_add_le_of_pairing (F : Y →ₗ[K] W)
    (tests : X →ₗ[K] Module.Dual K V) (seeds : Y →ₗ[K] V)
    (ht : Function.Injective tests) (hs : Function.Injective seeds)
    (silent : ∀ y, F y = 0 → ∀ x, tests x (seeds y) = 0) :
    finrank K F.ker + finrank K X ≤ finrank K V := by
  let C := tests.range.dualCoannihilator
  have hC (y : F.ker) : seeds (y : Y) ∈ C := by
    apply (Submodule.mem_dualCoannihilator _).mpr
    rintro _ ⟨x,rfl⟩
    exact silent _ (LinearMap.mem_ker.mp y.property) x
  let f : F.ker →ₗ[K] C :=
    LinearMap.codRestrict C (seeds.comp F.ker.subtype) hC
  have hf : Function.Injective f := by
    intro y y' e
    apply Subtype.ext
    apply hs
    exact congrArg Subtype.val e
  have he := LinearMap.finrank_le_finrank_of_injective hf
  have hdim := Subspace.finrank_add_finrank_dualCoannihilator_eq tests.range
  rw [LinearMap.finrank_range_of_inj ht] at hdim
  change finrank K F.ker ≤ finrank K tests.range.dualCoannihilator at he
  omega

end Pairing

/-- Polynomial multiplication with both finite degree bands named.
A zero polynomial is allowed in the definition; injectivity needs
the usual nonzero mask premise. -/
def paidHankel_mulDegreeBand (P : K[X]) (q : ℕ) :
    degreeLT K (q+1) →ₗ[K] degreeLT K (q+P.natDegree+1) :=
  LinearMap.codRestrict _ ((LinearMap.mulLeft K P).comp (degreeLT K (q+1)).subtype) (by
    intro Q
    change P*(Q : K[X]) ∈ degreeLT K (q+P.natDegree+1)
    have bound (f : K[X]) (n : ℕ) : f ∈ degreeLT K (n+1) ↔ f.degree ≤ (n : WithBot ℕ) := by
      rw [degreeLT_succ_eq_degreeLE,mem_degreeLE]
    have hd : (Q : K[X]).natDegree ≤ q :=
      natDegree_le_of_degree_le ((bound (Q : K[X]) q).mp Q.property)
    apply (bound (P*(Q : K[X])) (q+P.natDegree)).mpr
    exact degree_le_of_natDegree_le (natDegree_mul_le.trans (by omega)))

theorem paidHankel_mulDegreeBand_injective (P : K[X]) (q : ℕ) (hP : P ≠ 0) :
    Function.Injective (paidHankel_mulDegreeBand P q) := by
  intro Q T e
  apply Subtype.ext
  have h : P*(Q : K[X]) = P*(T : K[X]) := congrArg Subtype.val e
  exact mul_left_cancel₀ hP h

variable {s p q : ℕ} {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}

/-- Existing paid coefficient separation, exposed at the actual
ordinary Hankel with the literal mask 1. -/
theorem nodalPaidHankel_one_injective (ho : RKResearch.HasOrder p A b) (pay : 2*q+1 ≤ p) :
    Function.Injective (nodalPaidHankel A b (1 : K[X]) q) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro Q hQ
  have hi := (nodalColumn_paidGeometry ho).band_injective q pay
  apply (injective_iff_map_eq_zero _).mp hi Q
  change nodalColumn A (Q : K[X]) = 0
  have hmem : nodalColumn A (Q : K[X]) ∈ polyClockBand (nodalColumn A) q :=
    ⟨(Q : K[X]),Q.property,rfl⟩
  rw [polyClockBand_nodalColumn] at hmem
  obtain ⟨a,ha⟩ := hmem
  have hz := paid_coeffEval_eq_zero ho pay a (fun i => by
    have h := congrFun hQ i
    rw [nodalPaidHankel_apply,one_mul] at h
    rw [ha]
    exact h)
  rw [← ha,hz,map_zero]

private theorem nodalClock_monomial_one (i : ℕ) :
    nodalColumn A (monomial i 1 : K[X]) = normTree A (clockTree i) := by
  funext j
  simp only [nodalColumn_apply,Polynomial.eval_monomial,one_mul,normTree_clockTree]

private theorem nodalPair_mul_swap (L R U Q : K[X]) :
    nodalRow A b (L*U) (nodalColumn A (R*Q)) =
      nodalRow A b U (nodalColumn A ((L*R)*Q)) := by
  simp only [nodalRow_apply,nodalColumn_apply,Polynomial.eval_mul]
  apply Finset.sum_congr rfl
  intro i _
  ac_rfl

/-- A factorization gives a corank bound equal to the greater factor
degree. The exact mixed moment budget is the sum of both factor degrees,
not twice the greater degree, so this works also in odd mask degree. -/
theorem nodalPaidHankel_factor_corank_le (ho : RKResearch.HasOrder p A b)
    (L R : K[X]) (hL : L ≠ 0) (hR : R ≠ 0) (hle : L.natDegree ≤ R.natDegree)
    (pay : L.natDegree+R.natDegree+2*q+1 ≤ p) :
    finrank K (nodalPaidHankel A b (L*R) q).ker ≤ R.natDegree := by
  let D := degreeLT K (q+1)
  let V := degreeLT K (q+R.natDegree+1)
  letI : FiniteDimensional K V := (degreeLTEquiv K (q+R.natDegree+1)).symm.finiteDimensional
  let C : V →ₗ[K] (Fin s → K) := (nodalColumn A).comp V.subtype
  let f : D →ₗ[K] Module.Dual K V :=
    (C.dualMap.comp (nodalRow A b)).comp ((LinearMap.mulLeft K L).comp D.subtype)
  let g : D →ₗ[K] V := paidHankel_mulDegreeBand R q
  have hf : Function.Injective f := by
    apply (injective_iff_map_eq_zero _).mpr
    intro U hU
    apply (injective_iff_map_eq_zero _).mp (paidHankel_mulDegreeBand_injective L q hL) U
    apply (injective_iff_map_eq_zero _).mp
      (nodalPaidHankel_one_injective (q := q+L.natDegree) ho (by omega))
    rw [← nodalRow_hankel_eq A b (1 : K[X]) (q+L.natDegree)]
    funext i
    let j : Fin (q+R.natDegree+1) := ⟨i.val,by have := i.isLt; omega⟩
    let Y : V := ⟨monomial i.val 1,monomial_coe_mem_degreeLT j 1⟩
    have he := LinearMap.congr_fun hU Y
    change nodalRow A b (L*(U : K[X])) (nodalColumn A (monomial i.val 1 : K[X])) = 0 at he
    rw [nodalClock_monomial_one] at he
    change nodalRow A b (1*(L*(U : K[X]))) (normTree A (clockTree i.val)) = 0
    simpa only [one_mul] using he
  have hs : ∀ Q : D, nodalPaidHankel A b (L*R) q Q = 0 → ∀ U : D, f U (g Q) = 0 := by
    intro Q hQ U
    change nodalRow A b (L*(U : K[X])) (nodalColumn A (R*(Q : K[X]))) = 0
    rw [nodalPair_mul_swap]
    have hmem : nodalRow A b (U : K[X]) ∈ polyClockBand (nodalRow A b) q :=
      ⟨(U : K[X]),U.property,rfl⟩
    rw [polyClockBand_nodalRow] at hmem
    obtain ⟨a,ha⟩ := hmem
    rw [← ha]
    change (∑ i : Fin (q+1), a i • probe A b i.val) (nodalColumn A ((L*R)*(Q : K[X]))) = 0
    rw [LinearMap.sum_apply]
    apply Finset.sum_eq_zero
    intro i _
    have hz := congrFun hQ i
    rw [nodalPaidHankel_apply] at hz
    change probe A b i.val (nodalColumn A ((L*R)*(Q : K[X]))) = 0 at hz
    rw [LinearMap.smul_apply,hz,smul_zero]
  have d := finrank_ker_add_le_of_pairing (nodalPaidHankel A b (L*R) q) f g hf
    (paidHankel_mulDegreeBand_injective R q hR) hs
  have dD : finrank K D = q+1 :=
    (degreeLTEquiv K (q+1)).finrank_eq.trans (Module.finrank_fin_fun K)
  have dV : finrank K V = q+R.natDegree+1 :=
    (degreeLTEquiv K (q+R.natDegree+1)).finrank_eq.trans (Module.finrank_fin_fun K)
  rw [dD,dV] at d
  omega

/-- For the actual polynomial of any finite distinct-clock cover,
split the sites into halves and charge only the larger half. -/
theorem nodalPaidHankel_cutNodalPolynomial_corank_le (ho : RKResearch.HasOrder p A b)
    (U : Finset K) (pay : U.card+2*q+1 ≤ p) :
    finrank K (nodalPaidHankel A b (cutNodalPolynomial U) q).ker ≤ (U.card+1)/2 := by
  classical
  obtain ⟨S,hS,hdS⟩ := Finset.exists_subset_card_eq (s := U) (Nat.div_le_self U.card 2)
  let T := U \ S
  have hdT : T.card = U.card-S.card := Finset.card_sdiff_of_subset hS
  let L := cutNodalPolynomial S
  let R := cutNodalPolynomial T
  have hL : L ≠ 0 := cutNodalPolynomial_ne_zero S
  have hR : R ≠ 0 := cutNodalPolynomial_ne_zero T
  have h₁ : L.natDegree = U.card/2 := (natDegree_cutNodalPolynomial S).trans hdS
  have h₂ : R.natDegree = (U.card+1)/2 := by
    rw [show R.natDegree = T.card from natDegree_cutNodalPolynomial T,hdT,hdS]
    omega
  have hprod : L*R = cutNodalPolynomial U := by
    dsimp only [L,R,T,cutNodalPolynomial]
    rw [mul_comm,Finset.prod_sdiff hS]
  rw [← hprod,← h₂]
  exact nodalPaidHankel_factor_corank_le ho L R hL hR (by omega) (by omega)


/-- Ready-to-use per-width credit for the shared one-charge census. -/
theorem nodalPaidHankel_cutNodalPolynomial_rank_ge (ho : RKResearch.HasOrder p A b)
    (U : Finset K) (pay : U.card+2*q+1 ≤ p) :
    q+1-(U.card+1)/2 ≤ finrank K (nodalPaidHankel A b (cutNodalPolynomial U) q).range := by
  letI : FiniteDimensional K (degreeLT K (q+1)) := (degreeLTEquiv K (q+1)).symm.finiteDimensional
  have h := (nodalPaidHankel A b (cutNodalPolynomial U) q).finrank_range_add_finrank_ker
  have hd : finrank K (degreeLT K (q+1)) = q+1 :=
    (degreeLTEquiv K (q+1)).finrank_eq.trans (Module.finrank_fin_fun K)
  rw [hd] at h
  have hk := nodalPaidHankel_cutNodalPolynomial_corank_le (q := q) ho U pay
  omega
end
end RKResearch.Certified.Graded
