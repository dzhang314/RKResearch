module

public import RKCert.CompanionClearedCompound
public import RKCert.CompanionScaledMoment

@[expose] public section

/-! # Symbolic compound moments with an optional far-end factor

The normalized arithmetic kernel uses the exact determinant of the
standard companion minor with only its necessary denominator cleared.
A reflected factor is retained algebraically in the weight (1-X)^w. -/
namespace RKCert.Compound
open Module Polynomial Set Set.powersetCard RKCert.Endpoint RKCert.Paired.Signature
open scoped Classical
noncomputable section

variable {R S : Type*} [CommRing R] [CommRing S]

def rawMomentMatrix {n k : ℕ} (M j w : ℕ) (u : R) (b : Fin (n+1)→R) :
    Matrix (powersetCard (Fin n) k) (powersetCard (Fin n) k) R :=
  fun i t => scaledMoment M j (k+w) u ((1-X)^w*rawMinor b i t)

theorem rawMomentMatrix_map {n k : ℕ} (f : R→+*S)
    (M j w : ℕ) (u : R) (b : Fin (n+1)→R) :
    f.mapMatrix (rawMomentMatrix (k:=k) M j w u b) =
      rawMomentMatrix M j w (f u) (f ∘ b) := by
  apply Matrix.ext
  intro i t
  change f (scaledMoment M j (k+w) u ((1-X)^w*rawMinor b i t))=_
  rw [scaledMoment_map,Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_sub,
    Polynomial.map_one,Polynomial.map_X,rawMinor_map]
  rfl

variable {K : Type*} [Field K] [CharZero K]

def weightedMomentLinear (u : K) (j w : ℕ) : K[X] →ₗ[K] K :=
  (paidMomentLinear u j).comp (LinearMap.mulLeft K ((1-X)^w))

@[simp] theorem weightedMomentLinear_apply (u : K) (j w : ℕ) (P : K[X]) :
    weightedMomentLinear u j w P=paidMoment ((1-X)^w*P) u j := rfl

def factorWeightedOperator (q : K[X]) (k : ℕ) (u : K) (j w : ℕ) :
    (⋀[K]^k (AdjoinRoot q)) →ₗ[K] (⋀[K]^k (AdjoinRoot q)) :=
  ∑ i : Fin (k+1),
    weightedMomentLinear u j w (Lagrange.basis Finset.univ (factorSites K k) i) •
      exteriorPower.map k (shiftedRootOperator q (factorSites K k i))

theorem functional_interpolation (L : K[X] →ₗ[K] K) (P : K[X]) {k : ℕ}
    (hd : P.natDegree≤k) :
    L P=∑ i : Fin (k+1), P.eval (factorSites K k i) *
      L (Lagrange.basis Finset.univ (factorSites K k) i) := by
  have lt : P.degree<(Finset.univ : Finset (Fin (k+1))).card := by
    simp only [Finset.card_univ,Fintype.card_fin]
    exact P.degree_le_natDegree.trans_lt (by exact_mod_cast lt_of_le_of_lt hd (Nat.lt_succ_self k))
  have h := congrArg L (Lagrange.eq_interpolate (factorSites_injective k).injOn lt)
  rw [Lagrange.interpolate_apply,map_sum] at h
  simpa only [←smul_eq_C_mul,map_smul,smul_eq_mul] using h

theorem weightedOperator_toMatrix (q : K[X]) (hq : q.Monic) (k : ℕ)
    (u : K) (j w : ℕ) :
    LinearMap.toMatrix ((AdjoinRoot.powerBasis' hq).basis.exteriorPower k)
      ((AdjoinRoot.powerBasis' hq).basis.exteriorPower k) (factorWeightedOperator q k u j w) =
      ∑ i : Fin (k+1),
        weightedMomentLinear u j w (Lagrange.basis Finset.univ (factorSites K k) i) •
          orderedCompound k (Matrix.scalar _ (factorSites K k i)-coefficientCompanion q) := by
  rw [factorWeightedOperator,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul,exterior_toMatrix_eq_compound,shifted_root_matrix_entries]

theorem factor_weighted_eigenline (F G : K[X]) (F0 : F≠0) (GM : G.Monic) :
    ∃ z : ⋀[K]^G.natDegree (AdjoinRoot (F*G)),z≠0 ∧
      ∀ u : K,∀ j w : ℕ,factorWeightedOperator (F*G) G.natDegree u j w z=
        (paidMoment ((1-X)^w*G) u j) • z := by
  obtain ⟨z,nz,eigen⟩ := polynomial_factor_exterior_line F G F0 GM
  refine ⟨z,nz,fun u j w => ?_⟩
  simp only [factorWeightedOperator,LinearMap.sum_apply,LinearMap.smul_apply,eigen,smul_smul]
  rw [←Finset.sum_smul]
  congr 1
  simp_rw [mul_comm (_ : K) (G.eval _)]
  exact (functional_interpolation (weightedMomentLinear u j w) G le_rfl).symm

theorem normalized_raw_entry (q : K[X]) (hq : q.Monic) (b : Fin (q.natDegree+1)→K)
    (below : ∀ i : Fin q.natDegree,b i.castSucc=b (Fin.last q.natDegree)*q.coeff i.val)
    (M j k w : ℕ) (u : K) (un : u≠0) (s t : powersetCard (Fin q.natDegree) k)
    (nums : ∀ i : Fin (k+w+1),j+i.val+1∣M) :
    rawMomentMatrix M j w u b s t =
      (if hasLast t then b (Fin.last q.natDegree) else 1) *
        (LinearMap.toMatrix ((AdjoinRoot.powerBasis' hq).basis.exteriorPower k)
          ((AdjoinRoot.powerBasis' hq).basis.exteriorPower k)
          (((M:K)/u^(j+1)) • factorWeightedOperator q k u j w)) s t := by
  let P := rawMinor b s t
  have hp : P.natDegree≤k := rawMinor_outer_cap b s t
  have dk : ((1-X)^w*P).natDegree≤k+w := by
    apply natDegree_mul_le.trans
    have hw : ((1-X : K[X])^w).natDegree≤w := natDegree_pow_le.trans
      ((Nat.mul_le_mul_left w ((natDegree_sub_le _ _).trans (by simp))).trans_eq (Nat.mul_one w))
    omega
  unfold rawMomentMatrix
  rw [scaledMoment_eq_scale M j (k+w) u un _ dk nums,map_smul,weightedOperator_toMatrix]
  change (↑M/u^(j+1))*weightedMomentLinear u j w P=_
  rw [functional_interpolation (weightedMomentLinear u j w) P hp]
  let V : Fin (k+1) → Matrix (powersetCard (Fin q.natDegree) k)
      (powersetCard (Fin q.natDegree) k) K := fun i =>
    weightedMomentLinear u j w (Lagrange.basis Finset.univ (factorSites K k) i) •
      orderedCompound k (Matrix.scalar _ (factorSites K k i)-coefficientCompanion q)
  let B : K := if hasLast t then b (Fin.last q.natDegree) else 1
  let scale : K := (M:K)/u^(j+1)
  change scale * _=B*((scale • ∑ i,V i) s t)
  rw [Matrix.smul_apply scale (∑ i,V i) s t,smul_eq_mul,Matrix.sum_apply,
    mul_left_comm B scale]
  simp only [P,rawMinor_eval q b below]
  rw [Finset.mul_sum,Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [V,B]
  rw [Matrix.smul_apply,smul_eq_mul]
  ring

end
end RKCert.Compound
