module

public import RKCert.Dirk15ArithmeticNorms

@[expose] public section

/-! # Executable evaluation of the exact fixed Jacobi companion coefficients -/
namespace RKCert.FixedPolynomial
open Polynomial RKCert.Compound
open scoped Classical

def jacobiCoefficient (n i : ℕ) : ℤ :=
  (-1:ℤ)^(n+i+2)*(i+1)*((n+1).choose (i+1))*((n+i+2).choose (i+1))

theorem jacobiCoefficient_exact (n i : ℕ) :
    jacobiCoefficient n i=(integerJacobi n).coeff i :=
  (integerJacobi_coeff n i).symm

variable {R : Type*} [CommRing R]

def jacobiAt (n : ℕ) (u : R) : R :=
  (List.ofFn fun i : Fin (n+1) => (jacobiCoefficient n i.val:R)*u^i.val).sum

theorem jacobiAt_exact (n : ℕ) (u : R) :
    jacobiAt n u=(integerJacobi n).eval₂ (Int.castRingHom R) u := by
  rw [jacobiAt,List.sum_ofFn,←eval_map]
  let q := (integerJacobi n).map (Int.castRingHom R)
  have qd : q.natDegree≤n := natDegree_map_le.trans (integerJacobi_degree n).le
  change _=q.eval u
  conv_rhs => rw [q.as_sum_range' _ (Nat.lt_succ_of_le qd)]
  rw [eval_finsetSum,Finset.sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [eval_monomial,show q.coeff i.val=(jacobiCoefficient n i.val:R) by
    simp [q,coeff_map,jacobiCoefficient_exact]]

/-- Synthetic quotient coefficient, descending from the top zero
coefficient, with no division by the candidate's clock. -/
def syntheticCoefficient (p : ℕ→R) (u : R) : ℕ → ℕ → R
  | 0, _ => 0
  | m+1, i => p (i+1)+u*syntheticCoefficient p u m (i+1)

theorem syntheticCoefficient_exact (p : ℕ→R) (u : R) (Q : R[X])
    (h : ∀ i,Q.coeff i=p (i+1)+u*Q.coeff (i+1))
    (m i : ℕ) (top : Q.coeff (i+m)=0) :
    syntheticCoefficient p u m i=Q.coeff i := by
  induction m generalizing i with
  | zero => simpa only [Nat.add_zero,syntheticCoefficient] using top.symm
  | succ m ih =>
    rw [syntheticCoefficient,ih (i+1) (by rwa [show i+1+m=i+(m+1) by omega]),←h]

def nodeCoefficientsAt (n : ℕ) (u : R) (l : Fin (n+1)) : R :=
  let H := jacobiAt (n+1) u
  let L := jacobiAt n u
  let p := fun i => (jacobiCoefficient (n+1) i:R)*L-(jacobiCoefficient n i:R)*H
  syntheticCoefficient p u (n+1-l.val) l.val

def anchorCoefficientsAt (n : ℕ) (a : R) (l : Fin (n+2)) : R :=
  (jacobiCoefficient (n+1) l.val:R)+a*(jacobiCoefficient n l.val:R)

theorem nodeCoefficientsAt_exact (n : ℕ) (u : R) (l : Fin (n+1)) :
    nodeCoefficientsAt n u l=(nodeCoefficients n l).eval₂ (Int.castRingHom R) u := by
  let f := eval₂RingHom (Int.castRingHom R) u
  let H := integerJacobi (n+1)
  let L := integerJacobi n
  let Q := (universalOmission H L).map f
  let p := fun i => (jacobiCoefficient (n+1) i:R)*jacobiAt n u-(jacobiCoefficient n i:R)*jacobiAt (n+1) u
  have qn : Q.natDegree≤n := natDegree_map_le.trans
    (universalOmission_outer_cap H L (by simp [H,integerJacobi_degree]) (by simp [L,integerJacobi_degree]))
  have cP (P : ℤ[X]) : (P.map (C:ℤ→+*ℤ[X])).map f=P.map (Int.castRingHom R) := by
    rw [Polynomial.map_map,show f.comp (C : ℤ→+*ℤ[X])=Int.castRingHom R from eval₂RingHom_comp_C _ _]
  have q : (X-C u)*Q=C (jacobiAt n u)*(H.map (Int.castRingHom R))-
      C (jacobiAt (n+1) u)*(L.map (Int.castRingHom R)) := by
    have z := congrArg (Polynomial.map f) (universalOmission_mul H L)
    rw [Polynomial.map_mul,Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C,Polynomial.map_sub,
      Polynomial.map_mul,Polynomial.map_mul,Polynomial.map_C,Polynomial.map_C,cP H,cP L] at z
    have XF : f (X:ℤ[X])=u := by simp [f]
    have hF : f H=jacobiAt (n+1) u := (jacobiAt_exact (n+1) u).symm
    have lF : f L=jacobiAt n u := (jacobiAt_exact n u).symm
    simpa only [Q,XF,hF,lF] using z
  have stepCoeff (i : ℕ) : Q.coeff i=p (i+1)+u*Q.coeff (i+1) := by
    have qᵢ := congrArg (fun P : R[X] => P.coeff (i+1)) q
    rw [sub_mul,coeff_sub,coeff_X_mul,coeff_C_mul,coeff_sub,coeff_C_mul,coeff_C_mul] at qᵢ
    have hc : (H.map (Int.castRingHom R)).coeff (i+1)=(jacobiCoefficient (n+1) (i+1):R) := by
      rw [coeff_map,jacobiCoefficient_exact]
      rfl
    have lc : (L.map (Int.castRingHom R)).coeff (i+1)=(jacobiCoefficient n (i+1):R) := by
      rw [coeff_map,jacobiCoefficient_exact]
      rfl
    rw [hc,lc] at qᵢ
    have qᵢ : Q.coeff i-u*Q.coeff (i+1)=p (i+1) := by
      simpa only [p,mul_comm (jacobiAt n u),mul_comm (jacobiAt (n+1) u)] using qᵢ
    exact sub_eq_iff_eq_add.mp qᵢ
  change syntheticCoefficient p u (n+1-l.val) l.val=f ((universalOmission H L).coeff l.val)
  rw [syntheticCoefficient_exact p u Q stepCoeff _ _ (coeff_eq_zero_of_natDegree_lt (by have t:=l.isLt; omega))]
  exact coeff_map _ _

theorem anchorCoefficientsAt_exact (n : ℕ) (a : R) (l : Fin (n+2)) :
    anchorCoefficientsAt n a l=(anchorCoefficients n l).eval₂ (Int.castRingHom R) a := by
  unfold anchorCoefficients anchorCoefficientsAt parameterPencil
  rw [coeff_add,coeff_C_mul,coeff_map,coeff_map]
  simp only [eval₂_add,eval₂_C,eval₂_mul,eval₂_X,jacobiCoefficient_exact,
    Int.coe_castRingHom]

theorem nodeMomentNorm_at (n k j w : ℕ) (u : R) :
    (nodeMomentNorm n k j w).eval₂ (Int.castRingHom R) u=
      rawMomentNorm k order15Scale j w u (nodeCoefficientsAt n u) := by
  let f := eval₂RingHom (Int.castRingHom R) u
  change f (rawMomentNorm k order15Scale j w X (nodeCoefficients n))=_
  rw [rawMomentNorm_map,show f (X:ℤ[X])=u by simp [f]]
  congr 1
  funext i
  exact (nodeCoefficientsAt_exact n u i).symm

theorem nodeGramNorm_at (n k j w : ℕ) (u : R) :
    (nodeGramNorm n k j w).eval₂ (Int.castRingHom R) u=
      rawGramNorm k order15Scale j w u (nodeCoefficientsAt n u) := by
  let f := eval₂RingHom (Int.castRingHom R) u
  change f (rawGramNorm k order15Scale j w X (nodeCoefficients n))=_
  rw [rawGramNorm_map,show f (X:ℤ[X])=u by simp [f]]
  congr 1
  funext i
  exact (nodeCoefficientsAt_exact n u i).symm

theorem anchorMomentNorm_at (n k j : ℕ) (a : R) :
    (anchorMomentNorm n k j).eval₂ (Int.castRingHom R) a=
      rawMomentNorm k order15Scale j 0 1 (anchorCoefficientsAt n a) := by
  let f := eval₂RingHom (Int.castRingHom R) a
  change f (rawMomentNorm k order15Scale j 0 1 (anchorCoefficients n))=_
  rw [rawMomentNorm_map,map_one]
  congr 1
  funext i
  exact (anchorCoefficientsAt_exact n a i).symm

theorem anchorGramNorm_at (n k : ℕ) (a : R) :
    (anchorGramNorm n k).eval₂ (Int.castRingHom R) a=
      rawGramNorm k order15Scale 1 0 1 (anchorCoefficientsAt n a) := by
  let f := eval₂RingHom (Int.castRingHom R) a
  change f (rawGramNorm k order15Scale 1 0 1 (anchorCoefficients n))=_
  rw [rawGramNorm_map,map_one]
  congr 1
  funext i
  exact (anchorCoefficientsAt_exact n a i).symm

end RKCert.FixedPolynomial
