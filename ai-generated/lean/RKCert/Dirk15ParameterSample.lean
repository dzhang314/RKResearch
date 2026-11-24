module

public import RKCert.Dirk15ReadySample
public import RKCert.CompanionFastRemainder

@[expose] public section

/-! # Exact sampled evaluation of the two-ended parameter resultants

A polynomial of nominal degree up to 240 is reduced by the actual
monic degree-6/7 pencil. Each exact sample consequently pays just
one 11/13-dimensional packed Sylvester determinant. -/
namespace RKCert.FixedPolynomial
open Polynomial RKCert.LU RKCert.Compound RKCert.GoodPrimeDense
open scoped Classical
local notation "F" => ZMod 1009

def anchorLead (n : ℕ) : F := (jacobiCoefficient (n+1) (n+1):F)

def pencilLower (n : ℕ) (a : F) (i : Fin (n+1)) : F :=
  anchorCoefficientsAt n a i.castSucc / anchorLead n

noncomputable abbrev modPencil (n : ℕ) (a : F) : F[X] :=
  remainderModulus (pencilLower n a)

theorem anchorPencil_coeff (n : ℕ) (a : F) (i : Fin (n+2)) :
    ((integerJacobi (n+1)).map order15Reduce+C a*(integerJacobi n).map order15Reduce).coeff i.val=
      anchorCoefficientsAt n a i := by
  rw [coeff_add,coeff_C_mul,coeff_map,coeff_map,anchorCoefficientsAt,
    jacobiCoefficient_exact,jacobiCoefficient_exact]
  rfl

theorem anchorPencil_scaled (n : ℕ) (a : F) (lead : anchorLead n≠0) :
    (integerJacobi (n+1)).map order15Reduce+C a*(integerJacobi n).map order15Reduce=
      C (anchorLead n)*modPencil n a := by
  let E := (integerJacobi (n+1)).map order15Reduce+C a*(integerJacobi n).map order15Reduce
  have scaleCap : (C (anchorLead n)*modPencil n a).natDegree≤n+1 :=
    (natDegree_C_mul_le _ _).trans (remainderModulus_degree _).le
  have EC : E.natDegree≤n+1 := (natDegree_add_le _ _).trans (max_le
    (natDegree_map_le.trans (integerJacobi_degree _).le)
    ((natDegree_C_mul_le _ _).trans (natDegree_map_le.trans (by rw [integerJacobi_degree]; omega))))
  ext i
  change E.coeff i=_
  by_cases il : i<n+1
  · let j : Fin (n+1) := ⟨i,il⟩
    have e : E.coeff i=anchorCoefficientsAt n a j.castSucc := anchorPencil_coeff n a j.castSucc
    rw [e,coeff_C_mul,show (modPencil n a).coeff i=pencilLower n a j from low_coeff_of_remainderModulus _ j,
      pencilLower]
    field_simp [lead]
  · by_cases bi : i=n+1
    · subst i
      rw [coeff_C_mul,show (modPencil n a).coeff (n+1)=1 from
        (remainderModulus_degree (pencilLower n a)) ▸ (remainderModulus_monic (pencilLower n a)).coeff_natDegree,
        mul_one]
      have e : E.coeff (n+1)=anchorCoefficientsAt n a (Fin.last (n+1)) := anchorPencil_coeff n a (Fin.last (n+1))
      rw [e,anchorCoefficientsAt,Fin.val_last]
      have l0 : jacobiCoefficient n (n+1)=0 := by
        rw [jacobiCoefficient_exact,coeff_eq_zero_of_natDegree_lt (by rw [integerJacobi_degree]; omega)]
      simp [l0,anchorLead]
    · rw [coeff_eq_zero_of_natDegree_lt (EC.trans_lt (by omega)),
        coeff_eq_zero_of_natDegree_lt (scaleCap.trans_lt (by omega))]

def computeRemainder (n : ℕ) (a : F) (c : List ℕ) (i : Fin (n+1)) : F :=
  (residueRemainderArray (pencilLower n a) (c.map fun x : ℕ => (x:F)))[i.val]?.getD 0

theorem computeRemainder_exact (n : ℕ) (a : F) (c : List ℕ) :
    (residuePoly c)%ₘ(modPencil n a)=ofFn (n+1) (computeRemainder n a c) := by
  have e : computeRemainder n a c=residueHornerRemainder (pencilLower n a) (c.map fun x : ℕ => (x:F)) :=
    funext (fun i => residueRemainderArray_at _ _ i)
  rw [e]
  exact residueHornerRemainder_exact (R:=F) (pencilLower n a) (c.map fun x : ℕ => (x:F))

def modulusCoeff {n : ℕ} (b : Fin (n+1)→F) (s : ℕ) : F :=
  if h : s<n+1 then b ⟨s,h⟩ else if s=n+1 then 1 else 0

theorem modulusCoeff_exact {n : ℕ} (b : Fin (n+1)→F) (s : ℕ) :
    modulusCoeff b s=(remainderModulus b).coeff s := by
  by_cases h : s<n+1
  · rw [modulusCoeff,dite_eq_left h]
    exact (low_coeff_of_remainderModulus b ⟨s,h⟩).symm
  · rw [modulusCoeff,dite_eq_right h]
    by_cases e : s=n+1
    · subst s
      rw [ite_eq_left rfl]
      exact ((remainderModulus_degree b) ▸ (remainderModulus_monic b).coeff_natDegree).symm
    · rw [ite_eq_right e,coeff_eq_zero_of_natDegree_lt (by rw [remainderModulus_degree]; omega)]

def reducedSylvester {n : ℕ} (b r : Fin (n+1)→F) :
    Matrix (Fin (n+(n+1))) (Fin (n+(n+1))) F :=
  Matrix.of fun i j => j.addCases
    (fun f : Fin n => if f.val ≤ i.val ∧ i.val ≤ f.val+n+1 then modulusCoeff b (i.val-f.val) else 0)
    (fun f : Fin (n+1) => if h : f.val ≤ i.val ∧ i.val ≤ f.val+n then
      r ⟨i.val-f.val,by omega⟩ else 0)

theorem reducedSylvester_exact {n : ℕ} (b r : Fin (n+1)→F) :
    reducedSylvester b r=(ofFn (n+1) r).sylvester (remainderModulus b) n (n+1) := by
  ext i j
  induction j using Fin.addCases with
  | left j =>
    simp only [reducedSylvester,sylvester,Matrix.of_apply,Fin.addCases_left,Set.mem_Icc,
      Nat.add_assoc,modulusCoeff_exact]
  | right j =>
    simp only [reducedSylvester,sylvester,Matrix.of_apply,Fin.addCases_right,Set.mem_Icc]
    split_ifs with a
    · rw [ofFn_coeff_eq_val_of_lt _ (by omega)]
    · rfl

def numericParameterSylvester (n : ℕ) (a : F) (c : List ℕ) :
    Matrix (Fin (n+(n+1))) (Fin (n+(n+1))) F :=
  reducedSylvester (pencilLower n a) (computeRemainder n a c)

theorem parameterNorm_eval_from_rows (P : ℤ[X]) {d n : ℕ}
    (pCap : P.natDegree≤d) (dn : n+1≤d) (c : List ℕ)
    (reduced : P.map order15Reduce=residuePoly c) (a : F) (lead : anchorLead n≠0)
    (rows : Array ℕ) (v : F)
    (entry : ∀ i,packedRow (numericParameterSylvester n a c i)=get rows i.val)
    (paid : (rowMatrix 1009 (n+(n+1)) rows).det=v) :
    (parameterNorm P (integerJacobi (n+1)) (integerJacobi n) d (n+1)).eval₂ order15Reduce a=
      anchorLead n^d*(-1:F)^((n+1)*(d-n))*v := by
  have he : (numericParameterSylvester n a c).det=v := by
    apply of_rows _ rows v _ paid
    intro i j
    rw [←entry i,digit_packedRow]
  rw [parameterNorm_eval₂,anchorPencil_scaled n a lead,resultant_C_mul_right,
    resultant_remainder_of_monic _ _ (natDegree_map_le.trans pCap) (remainderModulus_monic _)
      (remainderModulus_degree _) (by omega) dn,Nat.add_sub_cancel,reduced,computeRemainder_exact]
  rw [show (ofFn (n+1) (computeRemainder n a c)).resultant (modPencil n a) n (n+1)=v from
    (congrArg Matrix.det (reducedSylvester_exact (pencilLower n a) _).symm).trans he]
  ring


def readyParameterSylvester (n : ℕ) (B R : Array ℕ) :
    Matrix (Fin (n+(n+1))) (Fin (n+(n+1))) F :=
  reducedSylvester (residueArray B : Fin (n+1)→F) (residueArray R)

theorem parameterGramNorm_eval_ready {n k j w : ℕ} (hn : 0<n) (hk : 0<k)
    (dn : n+1≤2*momentCap n k w) (c : List ℕ)
    (reduced : (nodeGramNorm n k j w).map order15Reduce=residuePoly c)
    (a : F) (lead : anchorLead n≠0) (rows B R : Array ℕ) (v : F)
    (hB : ∀ i,residueArray B i=pencilLower n a i)
    (hR : ∀ i,residueArray R i=computeRemainder n a c i)
    (entry : ∀ i,packedRow (readyParameterSylvester n B R i)=get rows i.val)
    (paid : (rowMatrix 1009 (n+(n+1)) rows).det=v) :
    (parameterGramNorm n k j w).eval₂ order15Reduce a=
      anchorLead n^(2*momentCap n k w)*(-1:F)^((n+1)*(2*momentCap n k w-n))*v := by
  unfold parameterGramNorm
  apply parameterNorm_eval_from_rows _ (nodeGramNorm_degree hn hk j w) dn c reduced a lead rows v _ paid
  have eq : readyParameterSylvester n B R=numericParameterSylvester n a c := by
    unfold readyParameterSylvester numericParameterSylvester
    rw [funext hB,funext hR]
  rw [←eq]
  exact entry

end RKCert.FixedPolynomial
