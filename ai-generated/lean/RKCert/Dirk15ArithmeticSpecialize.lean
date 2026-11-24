module

public import RKCert.Dirk15ArithmeticNorms
public import RKCert.Dirk15IntegerPencilShapes
public import RKCert.CompanionFieldSpecialization

@[expose] public section

/-! # Connect each standalone scalar condition to a fixed integer norm -/
namespace RKCert.FixedPolynomial
open Polynomial RKCert.Compound RKCert.Paired.Signature
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

local notation "φ" => Int.castRingHom K

private theorem omitted_data {n : ℕ} (hn : 0<n) {a u : K} {V : K[X]}
    (root : (fieldPencil K n a).eval u=0) (d : V∣fieldPencil K n a) (vU : V.eval u≠0) :
    let Q := omittedDifference (fieldJacobi K (n+1)) (fieldJacobi K n) u
    Q.natDegree=n ∧ Q≠0 ∧ V∣Q := by
  let Q := omittedDifference (fieldJacobi K (n+1)) (fieldJacobi K n) u
  have qd : Q.natDegree=n := omittedDifference_degree _ _ u (fieldJacobi_degree _)
    (fieldJacobi_degree n).le (fieldJacobi_omitted_low_nonzero root)
  exact ⟨qd,fun z=>by change Q=0 at z; rw [z,natDegree_zero] at qd; omega,
    omitted_factor_no_endpoint _ _ u a root d vU⟩

theorem nodeMomentNorm_zero {n k j w : ℕ} (hn : 0<n) (den : j+k+w+1≤10)
    {a u : K} (un : u≠0) {V : K[X]} (vd : V.natDegree=k)
    (root : (fieldPencil K n a).eval u=0) (d : V∣fieldPencil K n a)
    (vU : V.eval u≠0) (paid : paidMoment ((1-X)^w*V) u j=0) :
    (nodeMomentNorm n k j w).eval₂ φ u=0 := by
  let Q := omittedDifference (fieldJacobi K (n+1)) (fieldJacobi K n) u
  obtain ⟨qd,q0,qdiv⟩ := omitted_data hn root d vU
  let F := eval₂RingHom φ u
  change F (rawMomentNorm k order15Scale j w X (nodeCoefficients n))=0
  rw [rawMomentNorm_map]
  have f0 : F (X:ℤ[X])=u := by simp [F]
  have coeffs : F ∘ nodeCoefficients n=fun t => Q.coeff t.val := by
    funext l
    exact universalOmission_coeff_specializes _ _ φ u l.val
  rw [f0,coeffs]
  exact rawMomentNorm_specialized_zero Q V q0 (fun e=>vU (by simp [e])) qd vd qdiv u un
    (factorial_scale_clears (by omega)) paid

theorem nodeGramNorm_zero {n k j w : ℕ} (hn : 0<n) (den : j+k+w+3≤10)
    {a u : K} (un : u≠0) {V : K[X]} (vd : V.natDegree=k)
    (root : (fieldPencil K n a).eval u=0) (d : V∣fieldPencil K n a)
    (vU : V.eval u≠0)
    (paid : paidMoment ((1-X)^w*V) u j*paidMoment ((1-X)^w*V) u (j+2)-
      (paidMoment ((1-X)^w*V) u (j+1))^2=0) :
    (nodeGramNorm n k j w).eval₂ φ u=0 := by
  let Q := omittedDifference (fieldJacobi K (n+1)) (fieldJacobi K n) u
  obtain ⟨qd,q0,qdiv⟩ := omitted_data hn root d vU
  let F := eval₂RingHom φ u
  change F (rawGramNorm k order15Scale j w X (nodeCoefficients n))=0
  rw [rawGramNorm_map]
  have f0 : F (X:ℤ[X])=u := by simp [F]
  have coeffs : F ∘ nodeCoefficients n=fun t => Q.coeff t.val := by
    funext l
    exact universalOmission_coeff_specializes _ _ φ u l.val
  rw [f0,coeffs]
  exact rawGramNorm_specialized_zero Q V q0 (fun e=>vU (by simp [e])) qd vd qdiv u un
    (fun l l2 => factorial_scale_clears (by omega)) paid

omit [CharZero K] in
private theorem anchorCoefficients_spec (n : ℕ) (a : K) :
    (eval₂RingHom φ a) ∘ anchorCoefficients n=fun l => (fieldPencil K n a).coeff l.val := by
  funext l
  change ((parameterPencil _ _).coeff l.val).eval₂ φ a=_
  rw [parameterPencil,coeff_add,coeff_C_mul,coeff_map,coeff_map]
  change _=(fieldJacobi K (n+1)+C a*fieldJacobi K n).coeff l.val
  simp only [eval₂_add,eval₂_mul,eval₂_C,eval₂_X,coeff_add,coeff_C_mul,fieldJacobi,coeff_map]

theorem anchorMomentNorm_zero {n k j : ℕ} (den : j+k+1≤10) {a : K} {V : K[X]} (V0 : V≠0)
    (vd : V.natDegree=k) (d : V∣fieldPencil K n a) (paid : paidMoment V 1 j=0) :
    (anchorMomentNorm n k j).eval₂ φ a=0 := by
  let F := eval₂RingHom φ a
  let Q := fieldPencil K n a
  have qd : Q.natDegree=n+1 := fieldPencil_degree n a
  have q0 : Q≠0 := fun z=>by rw [z,natDegree_zero] at qd; omega
  change F (rawMomentNorm (n:=n+1) k order15Scale j 0 1 (anchorCoefficients n))=0
  rw [rawMomentNorm_map,map_one,anchorCoefficients_spec]
  exact rawMomentNorm_specialized_zero Q V q0 V0 qd vd d 1 one_ne_zero
    (factorial_scale_clears (by omega)) (by simpa only [pow_zero,one_mul] using paid)

theorem anchorGramNorm_zero {n k : ℕ} (den : k+4≤10) {a : K} {V : K[X]} (V0 : V≠0)
    (vd : V.natDegree=k) (d : V∣fieldPencil K n a)
    (paid : paidMoment V 1 1*paidMoment V 1 3-(paidMoment V 1 2)^2=0) :
    (anchorGramNorm n k).eval₂ φ a=0 := by
  let F := eval₂RingHom φ a
  let Q := fieldPencil K n a
  have qd : Q.natDegree=n+1 := fieldPencil_degree n a
  have q0 : Q≠0 := fun z=>by rw [z,natDegree_zero] at qd; omega
  change F (rawGramNorm (n:=n+1) k order15Scale 1 0 1 (anchorCoefficients n))=0
  rw [rawGramNorm_map,map_one,anchorCoefficients_spec]
  exact rawGramNorm_specialized_zero Q V q0 V0 qd vd d 1 one_ne_zero
    (fun l l2 => factorial_scale_clears (by omega)) (by simpa only [pow_zero,one_mul] using paid)

theorem parameterGramNorm_zero {n k j w : ℕ} (hn : 0<n) (hk : 0<k) (den : j+k+w+3≤10)
    {a u : K} (un : u≠0) {V : K[X]} (vd : V.natDegree=k)
    (root : (fieldPencil K n a).eval u=0) (d : V∣fieldPencil K n a)
    (vU : V.eval u≠0)
    (paid : paidMoment ((1-X)^w*V) u j*paidMoment ((1-X)^w*V) u (j+2)-
      (paidMoment ((1-X)^w*V) u (j+1))^2=0) :
    (parameterGramNorm n k j w).eval₂ φ a=0 := by
  apply parameterNorm_zero_of_common_root φ _ _ _ (nodeGramNorm_degree hn hk _ _)
  · rw [integerJacobi_degree]
  · rw [integerJacobi_degree]; omega
  · exact Or.inr (by omega)
  · rw [eval_map]
    exact nodeGramNorm_zero hn den un vd root d vU paid
  · exact root

end
end RKCert.FixedPolynomial
