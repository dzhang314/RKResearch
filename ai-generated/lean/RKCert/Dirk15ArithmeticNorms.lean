module

public import RKCert.CompanionRawNorm
public import RKCert.PencilOmissionDegree
public import RKCert.Dirk15IntegerJacobi
public import RKCert.ResultantSmallRemainder

@[expose] public section

/-! # The exact integer polynomials of the order-fifteen arithmetic

All variables are formal. The node polynomials, fixed-anchor polynomials,
and parameter resultants are built before reduction to a prime field.
These definitions and structural degree caps do not assert modular
coprimality. -/
namespace RKCert.FixedPolynomial
open Polynomial RKCert.Compound
open scoped Classical
noncomputable section

def order15Scale : ℕ := Nat.factorial 10

def nodeCoefficients (n : ℕ) (l : Fin (n+1)) : ℤ[X] :=
  (universalOmission (integerJacobi (n+1)) (integerJacobi n)).coeff l.val

def anchorCoefficients (n : ℕ) (l : Fin (n+2)) : ℤ[X] :=
  (parameterPencil (integerJacobi (n+1)) (integerJacobi n)).coeff l.val

def nodeMomentNorm (n k j w : ℕ) : ℤ[X] :=
  rawMomentNorm k order15Scale j w X (nodeCoefficients n)

def nodeGramNorm (n k j w : ℕ) : ℤ[X] :=
  rawGramNorm k order15Scale j w X (nodeCoefficients n)

def anchorMomentNorm (n k j : ℕ) : ℤ[X] :=
  rawMomentNorm (n:=n+1) k order15Scale j 0 1 (anchorCoefficients n)

def anchorGramNorm (n k : ℕ) : ℤ[X] :=
  rawGramNorm (n:=n+1) k order15Scale 1 0 1 (anchorCoefficients n)

def momentCap (n k w : ℕ) : ℕ :=
  (k+w)*n.choose k+n*(n-1).choose (k-1)

def parameterGramNorm (n k j w : ℕ) : ℤ[X] :=
  parameterNorm (nodeGramNorm n k j w) (integerJacobi (n+1)) (integerJacobi n)
    (2*momentCap n k w) (n+1)

def minusParameter (P : ℤ[X]) : ℤ[X] := P.comp (-X)

theorem minusParameter_degree (P : ℤ[X]) : (minusParameter P).natDegree≤P.natDegree := by
  unfold minusParameter
  exact natDegree_comp_le.trans (by rw [natDegree_neg,natDegree_X,mul_one])

theorem minusParameter_eval₂ {K : Type*} [CommRing K] (f : ℤ →+* K) (P : ℤ[X]) (a : K) :
    (minusParameter P).eval₂ f a=P.eval₂ f (-a) := by
  simp [minusParameter,eval₂_comp,eval₂_neg]

theorem nodeCoefficients_cap (n : ℕ) (l : Fin (n+1)) :
    (nodeCoefficients n l).natDegree≤n := by
  apply universalOmission_coeff_cap
  · rw [integerJacobi_degree]
  · rw [integerJacobi_degree]
    omega

theorem anchorCoefficients_cap (n : ℕ) (l : Fin (n+2)) :
    (anchorCoefficients n l).natDegree≤1 := by
  unfold anchorCoefficients parameterPencil
  rw [coeff_add,coeff_C_mul,coeff_map,coeff_map]
  exact (natDegree_add_le _ _).trans
    (max_le (by simp) (natDegree_mul_le.trans (by simp)))

theorem nodeMomentNorm_degree {n k : ℕ} (hn : 0<n) (hk : 0<k) (j w : ℕ) :
    (nodeMomentNorm n k j w).natDegree≤momentCap n k w := by
  simpa only [nodeMomentNorm,momentCap,Nat.one_mul] using
    rawMomentNorm_degree hn hk order15Scale j w (natDegree_X_le (R:=ℤ)) (nodeCoefficients n)
      (nodeCoefficients_cap n)

theorem nodeGramNorm_degree {n k : ℕ} (hn : 0<n) (hk : 0<k) (j w : ℕ) :
    (nodeGramNorm n k j w).natDegree≤2*momentCap n k w := by
  simpa only [nodeGramNorm,momentCap,Nat.one_mul] using
    rawGramNorm_degree hn hk order15Scale j w (natDegree_X_le (R:=ℤ)) (nodeCoefficients n)
      (nodeCoefficients_cap n)

theorem anchorMomentNorm_degree (n : ℕ) {k : ℕ} (hk : 0<k) (j : ℕ) :
    (anchorMomentNorm n k j).natDegree≤n.choose (k-1) := by
  simpa only [anchorMomentNorm,Nat.zero_mul,Nat.zero_add,Nat.one_mul,Nat.succ_sub_one,Nat.add_sub_cancel] using
    rawMomentNorm_degree (Nat.succ_pos n) hk order15Scale j 0 (u:=(1:ℤ[X])) (U:=0)
      (by simp) (anchorCoefficients n) (anchorCoefficients_cap n)

theorem anchorGramNorm_degree (n : ℕ) {k : ℕ} (hk : 0<k) :
    (anchorGramNorm n k).natDegree≤2*n.choose (k-1) := by
  simpa only [anchorGramNorm,Nat.zero_mul,Nat.zero_add,Nat.one_mul,Nat.succ_sub_one,Nat.add_sub_cancel] using
    rawGramNorm_degree (Nat.succ_pos n) hk order15Scale 1 0 (u:=(1:ℤ[X])) (U:=0)
      (by simp) (anchorCoefficients n) (anchorCoefficients_cap n)

theorem parameterGramNorm_degree (n k j w : ℕ) :
    (parameterGramNorm n k j w).natDegree≤2*momentCap n k w :=
  parameterNorm_degree_le _ _ _ _ _

end
end RKCert.FixedPolynomial
