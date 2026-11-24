module

public import RKCert.EndpointJacobiTwoBand

@[expose] public section

/-! # The adjacent three-term recurrence, through every characteristic-zero field -/
namespace RKCert.Paired
open Polynomial
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

theorem jacobiPair_add (P Q R : K[X]) : jacobiPair (P+Q) R=jacobiPair P R+jacobiPair Q R := by
  simp only [jacobiPair,mul_add,add_mul,map_add]

theorem jacobiTwo_raise_monic (n : ℕ) :
    (X*jacobiTwo K n).Monic ∧ (X*jacobiTwo K n).natDegree=n+1 := by
  have mon := monic_X.mul (jacobiTwo_monic (K:=K) n)
  have deg := natDegree_mul X_ne_zero (jacobiTwo_monic (K:=K) n).ne_zero
  rw [natDegree_X,jacobiTwo_degree,add_comm] at deg
  exact ⟨mon,deg⟩

theorem jacobiTwo_raise_diff (n : ℕ) :
    (X*jacobiTwo K n-jacobiTwo K (n+1)).natDegree≤n := by
  have coeff : (X*jacobiTwo K n).coeff (n+1)=1 := by
    nth_rw 1 [←(jacobiTwo_raise_monic (K:=K) n).2]
    exact (jacobiTwo_raise_monic (K:=K) n).1
  have bound := jacobiTwo_strip (Nat.succ_pos n) (jacobiTwo_raise_monic (K:=K) n).2.le
  rw [coeff,map_one,one_mul] at bound
  exact bound

theorem jacobiTwo_three_term (n : ℕ) (hn : 2≤n) :
    ∃ a b : K, b≠0 ∧
      X*jacobiTwo K n=jacobiTwo K (n+1)+C a*jacobiTwo K n+C b*jacobiTwo K (n-1) := by
  let P := X*jacobiTwo K n-jacobiTwo K (n+1)
  let lo := jacobiTwo K (n-1)
  let J := jacobiTwo K n
  have dP : P.natDegree≤n := jacobiTwo_raise_diff n
  have test (Q : K[X]) (q : Q.natDegree≤n-2) : jacobiPair P Q=0 := by
    have dq : (X*Q).natDegree<n := by
      have m := natDegree_mul_le (p:=(X:K[X])) (q:=Q)
      rw [natDegree_X] at m
      omega
    change jacobiPair (X*J-jacobiTwo K (n+1)) Q=0
    rw [jacobiPair_sub,jacobiPair_mul_X,jacobiPair_orthogonal _ _ dq,
      jacobiPair_orthogonal _ _ (by omega : Q.natDegree<n+1),sub_self]
  obtain ⟨a,b,be⟩ := jacobiTwo_top_two hn dP test
  have signal : jacobiPair P lo=jacobiPair J J := by
    have low : lo.natDegree=n-1 := jacobiTwo_degree (n-1)
    change jacobiPair (X*J-jacobiTwo K (n+1)) lo=_
    rw [jacobiPair_sub,jacobiPair_mul_X,jacobiPair_orthogonal _ _ (by omega : lo.natDegree<n+1),sub_zero]
    let R := X*lo-J
    have deg : R.natDegree<n := by
      have h := jacobiTwo_raise_diff (K:=K) (n-1)
      have e : (n-1)+1=n := by omega
      rw [e] at h
      change R.natDegree≤n-1 at h
      omega
    have eq := jacobiPair_sub (X*lo) J J
    have r0 : jacobiPair R J=0 := by
      rw [jacobiPair_symm]
      exact jacobiPair_orthogonal n R deg
    change jacobiPair R J=jacobiPair (X*lo) J-jacobiPair J J at eq
    rw [r0] at eq
    rw [jacobiPair_symm J (X*lo)]
    exact sub_eq_zero.mp eq.symm
  refine ⟨a,b,?_,?_⟩
  · intro bn
    have dl : lo.natDegree=n-1 := jacobiTwo_degree (n-1)
    rw [be,jacobiPair_add,jacobiPair_C_mul,jacobiPair_C_mul,bn,zero_mul,
      jacobiPair_orthogonal _ _ (by omega : lo.natDegree<n),mul_zero,add_zero] at signal
    exact jacobiTwo_diagonal_ne n signal.symm
  · change X*J=jacobiTwo K (n+1)+C a*J+C b*lo
    change X*J-jacobiTwo K (n+1)=C a*J+C b*lo at be
    linear_combination be

end
end RKCert.Paired
