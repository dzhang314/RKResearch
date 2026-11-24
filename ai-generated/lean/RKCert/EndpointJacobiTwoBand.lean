module

public import RKCert.EndpointJacobiTwo

@[expose] public section

/-! # Short high-degree Jacobi bands and nonzero adjacent recurrence

The short bands are obtained from exact leading-coefficient subtraction
and the algebraic two-endpoint Hilbert tests. No quadrature is hidden in
these auxiliary polynomial theorems.
-/
namespace RKCert.Paired
open Polynomial RKCert.Endpoint
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

def jacobiPair (P Q : K[X]) : K := unitIntegral ((X*(1-X))*P*Q)

theorem jacobiPair_symm (P Q : K[X]) : jacobiPair P Q=jacobiPair Q P := by
  unfold jacobiPair
  congr 1
  ac_rfl

theorem jacobiPair_mul_X (P Q : K[X]) : jacobiPair (X*P) Q=jacobiPair P (X*Q) := by
  unfold jacobiPair
  congr 1
  ac_rfl

theorem jacobiPair_sub (P Q R : K[X]) : jacobiPair (P-Q) R=jacobiPair P R-jacobiPair Q R := by
  simp only [jacobiPair,mul_sub,sub_mul,map_sub]

theorem jacobiPair_C_mul (a : K) (P Q : K[X]) : jacobiPair (C a*P) Q=a*jacobiPair P Q := by
  unfold jacobiPair
  rw [show (X*(1-X))*(C a*P)*Q=a • ((X*(1-X))*P*Q) by rw [smul_eq_C_mul]; ac_rfl,
    map_smul,smul_eq_mul]

theorem jacobiPair_orthogonal (n : ℕ) (P : K[X]) (d : P.natDegree<n) :
    jacobiPair (jacobiTwo K n) P=0 :=
  jacobiTwo_orthogonal n P d

theorem jacobiPair_detect (P : K[X]) {d : ℕ} (bound : P.natDegree≤d)
    (quiet : ∀ Q : K[X],Q.natDegree≤d → jacobiPair P Q=0) : P=0 := by
  apply two_end_weight_primitive_detect P (k:=1) bound
  intro i
  change unitIntegral (X^(1+i.val)*((1-X)*P))=0
  rw [show X^(1+i.val)*((1-X)*P)=X*(1-X)*P*X^i.val by rw [pow_add,pow_one]; ring]
  exact quiet (X^i.val) (by rw [natDegree_X_pow]; have := i.isLt; omega)

set_option maxHeartbeats 600000 in
theorem jacobiTwo_strip {P : K[X]} {d : ℕ} (pos : 0<d) (deg : P.natDegree≤d) :
    (P-C (P.coeff d)*jacobiTwo K d).natDegree≤d-1 := by
  let R := P-C (P.coeff d)*jacobiTwo K d
  have rr : R.natDegree≤d := (natDegree_sub_le _ _).trans
    (max_le deg ((natDegree_C_mul_le _ _).trans (jacobiTwo_degree d).le))
  have c : (jacobiTwo K d).coeff d=1 := calc
    _ = (jacobiTwo K d).coeff (jacobiTwo K d).natDegree :=
      congrArg (fun k => (jacobiTwo K d).coeff k) (jacobiTwo_degree d).symm
    _ = (jacobiTwo K d).leadingCoeff := coeff_natDegree
    _ = 1 := jacobiTwo_monic d
  have z : R.coeff d=0 := by
    change (P-C (P.coeff d)*jacobiTwo K d).coeff d=0
    rw [coeff_sub,coeff_C_mul,c,mul_one,sub_self]
  change R.natDegree≤d-1
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  by_cases e : j=d
  · rwa [e]
  · exact coeff_eq_zero_of_natDegree_lt (by omega)

theorem jacobiTwo_strip_quiet {P : K[X]} {d t : ℕ}
    (td : t<d) (quiet : ∀ Q : K[X],Q.natDegree≤t → jacobiPair P Q=0) :
    ∀ Q : K[X],Q.natDegree≤t → jacobiPair (P-C (P.coeff d)*jacobiTwo K d) Q=0 := by
  intro Q q
  rw [jacobiPair_sub,jacobiPair_C_mul,quiet Q q,jacobiPair_orthogonal _ _ (q.trans_lt td),
    mul_zero,sub_self]

theorem jacobiTwo_top_one {P : K[X]} {d : ℕ} (n : 0<d) (deg : P.natDegree≤d)
    (quiet : ∀ Q : K[X],Q.natDegree≤d-1 → jacobiPair P Q=0) :
    P=C (P.coeff d)*jacobiTwo K d :=
  sub_eq_zero.mp (jacobiPair_detect _ (jacobiTwo_strip n deg)
    (jacobiTwo_strip_quiet (by omega) quiet))

theorem jacobiTwo_top_two {P : K[X]} {d : ℕ} (n : 2≤d) (deg : P.natDegree≤d)
    (quiet : ∀ Q : K[X],Q.natDegree≤d-2 → jacobiPair P Q=0) :
    ∃ a b : K, P=C a*jacobiTwo K d+C b*jacobiTwo K (d-1) := by
  let T := P-C (P.coeff d)*jacobiTwo K d
  have t : T.natDegree≤d-1 := jacobiTwo_strip (by omega : 0<d) deg
  have q : ∀ Q : K[X],Q.natDegree≤(d-1)-1 → jacobiPair T Q=0 := by
    have e : (d-1)-1=d-2 := by omega
    rw [e]
    exact jacobiTwo_strip_quiet (by omega) quiet
  have ht := jacobiTwo_top_one (by omega) t q
  refine ⟨P.coeff d,T.coeff (d-1),?_⟩
  rw [←ht]
  dsimp only [T]
  abel

theorem jacobiTwo_diagonal_ne (n : ℕ) :
    jacobiPair (jacobiTwo K n) (jacobiTwo K n)≠0 := by
  intro z
  apply (jacobiTwo_monic (K:=K) n).ne_zero
  apply jacobiPair_detect _ (jacobiTwo_degree n).le
  intro Q dQ
  let R := Q-C (Q.coeff n)*jacobiTwo K n
  by_cases n0 : n=0
  · subst n
    have q : Q=C (Q.coeff 0) := eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero dQ)
    have u : jacobiTwo K 0=1 := (jacobiTwo_monic 0).natDegree_eq_zero.mp (jacobiTwo_degree 0)
    rw [jacobiPair_symm,q,show C (Q.coeff 0)=C (Q.coeff 0)*jacobiTwo K 0 by simp [u],
      jacobiPair_C_mul,z,mul_zero]
  · have dR := jacobiTwo_strip (by omega : 0<n) dQ
    change R.natDegree≤n-1 at dR
    have eq := jacobiPair_sub Q (C (Q.coeff n)*jacobiTwo K n) (jacobiTwo K n)
    rw [jacobiPair_C_mul,z,mul_zero,sub_zero] at eq
    rw [jacobiPair_symm (jacobiTwo K n) Q,←eq,show Q-C (Q.coeff n)*jacobiTwo K n=R from rfl,
      jacobiPair_symm, jacobiPair_orthogonal _ _ (by omega)]

end
end RKCert.Paired
