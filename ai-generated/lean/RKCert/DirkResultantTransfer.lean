module

public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.ZMod

@[expose] public section

/-! # Exact good-prime transfer for fixed integer resultant certificates
No unknown RK coefficient or free Jacobi parameter is specialized. Instead
degree-preserving reduction validates a *fixed integer resultant*. -/
namespace RKCert.FixedPolynomial
open Polynomial

variable {R : Type*} [CommRing R]

/-- The exact Sylvester determinant at the specified degree bounds is zero
at any common root over the same ring. -/
theorem resultant_zero_of_common_eval {F G : R[X]} {m n : ℕ}
    (hF : F.natDegree≤m) (hG : G.natDegree≤n) (h : m≠0 ∨ n≠0)
    {u : R} (huF : F.eval u=0) (huG : G.eval u=0) : F.resultant G m n=0 := by
  obtain ⟨P,Q,_,_,e⟩ := exists_mul_add_mul_eq_C_resultant F G hF hG h
  have he := congrArg (Polynomial.eval u) e
  simpa only [eval_add,eval_mul,eval_C,huF,huG,zero_mul,add_zero] using he.symm

/-- A modular coprimality certificate proves no common zero in *any*
characteristic-zero field provided both reductions attain the declared
integer degree caps. Checking finite-field evaluation alone is not enough. -/
theorem no_common_eval_of_good_prime {q : ℕ} [Fact q.Prime]
    (F G : ℤ[X]) (m n : ℕ) (hF : F.natDegree≤m) (hG : G.natDegree≤n)
    (mF : (F.map (Int.castRingHom (ZMod q))).natDegree=m)
    (mG : (G.map (Int.castRingHom (ZMod q))).natDegree=n)
    (hpos : m≠0 ∨ n≠0)
    (co : IsCoprime (F.map (Int.castRingHom (ZMod q))) (G.map (Int.castRingHom (ZMod q))))
    {K : Type*} [Field K] [CharZero K] (u : K) :
    (F.map (Int.castRingHom K)).eval u≠0 ∨ (G.map (Int.castRingHom K)).eval u≠0 := by
  let φ := Int.castRingHom (ZMod q)
  let ψ := Int.castRingHom K
  have hmod : (F.map φ).resultant (G.map φ) m n≠0 := by
    rw [←mF,←mG]
    exact Polynomial.resultant_ne_zero _ _ co
  have hZ : F.resultant G m n≠0 := by
    intro he
    exact hmod (by rw [resultant_map_map,he,map_zero])
  have hK : (F.map ψ).resultant (G.map ψ) m n≠0 := by
    rw [resultant_map_map]
    exact fun he => hZ ((map_eq_zero_iff ψ Int.cast_injective).mp he)
  by_contra! hn
  exact hK (resultant_zero_of_common_eval (natDegree_map_le.trans hF)
    (natDegree_map_le.trans hG) hpos hn.1 hn.2)

/-- An outer polynomial in the node, with coefficients polynomials in the
free parameter. Neither variable is sampled in this definition. -/
noncomputable def parameterPencil (H L : R[X]) : R[X][X] :=
  H.map (C : R →+* R[X]) + C (X : R[X])*L.map (C : R →+* R[X])

noncomputable def parameterNorm (F H L : R[X]) (m n : ℕ) : R[X] :=
  (F.map (C : R →+* R[X])).resultant (parameterPencil H L) m n

/-- The integer degree bound is structural: the first m Sylvester
columns are affine in the parameter, and the remaining n are constant. -/
theorem parameterNorm_degree_le (F H L : R[X]) (m n : ℕ) :
    (parameterNorm F H L m n).natDegree≤m := by
  classical
  let M := sylvester (F.map (C:R→+*R[X])) (parameterPencil H L) m n
  change M.det.natDegree≤m
  rw [Matrix.det_apply]
  apply natDegree_sum_le_of_forall_le
  intro σ _
  apply (natDegree_smul_le _ _).trans
  apply (natDegree_prod_le Finset.univ _).trans
  rw [Fin.sum_univ_add]
  have ha (i : Fin m) : (M (σ (i.castAdd n)) (i.castAdd n)).natDegree≤1 := by
    dsimp [M,sylvester]
    rw [Fin.addCases_left]
    split_ifs
    · rw [parameterPencil,coeff_add,coeff_C_mul,coeff_map,coeff_map]
      exact (natDegree_add_le _ _).trans (max_le (by simp)
        (natDegree_mul_le.trans (by simpa only [natDegree_C,add_zero] using (natDegree_X_le (R:=R)))))
    · simp
  have hb (j : Fin n) : (M (σ (j.natAdd m)) (j.natAdd m)).natDegree≤0 := by
    dsimp [M,sylvester]
    rw [Fin.addCases_right]
    split_ifs <;> (try rw [coeff_map]) <;> simp
  refine (add_le_add (Finset.sum_le_sum fun i _ => ha i) (Finset.sum_le_sum fun j _ => hb j)).trans ?_
  simp

/-- Exact change of coefficient ring in the free-parameter norm. -/
theorem parameterNorm_map {S : Type*} [CommRing S] (φ : R →+* S)
    (F H L : R[X]) (m n : ℕ) :
    (parameterNorm F H L m n).map φ=parameterNorm (F.map φ) (H.map φ) (L.map φ) m n := by
  unfold parameterNorm parameterPencil
  let φP : R[X] →+* S[X] := mapRingHom φ
  change φP ((F.map C).resultant ((H.map C)+C X*L.map C) m n)=_
  rw [←resultant_map_map]
  change ((F.map C).map (mapRingHom φ)).resultant
    (((H.map C)+C X*L.map C).map (mapRingHom φ)) m n=_
  congr 1
  · rw [Polynomial.map_map,Polynomial.map_map]
    congr 1
    ext a
    simp
  · rw [Polynomial.map_add,Polynomial.map_mul,Polynomial.map_C,
      show (mapRingHom φ) X=X from Polynomial.map_X _]
    congr 1 <;> rw [Polynomial.map_map,Polynomial.map_map] <;> congr 1 <;> ext a <;> simp

/-- A genuine node root of both the fixed norm and the pencil forces the
parameter norm to vanish. All Sylvester degrees are held fixed. -/
theorem parameterNorm_zero_of_common_root {S : Type*} [CommRing S]
    (φ : R →+* S) (F H L : R[X]) {m n : ℕ} (hm : F.natDegree≤m)
    (hH : H.natDegree≤n) (hL : L.natDegree≤n) (hp : m≠0 ∨ n≠0)
    {u a : S} (hF : (F.map φ).eval u=0)
    (hP : ((H.map φ)+C a*(L.map φ)).eval u=0) :
    (parameterNorm F H L m n).eval₂ φ a=0 := by
  let ψ := eval₂RingHom φ a
  have hc : ψ.comp (C : R →+* R[X])=φ := eval₂RingHom_comp_C _ _
  have hP' : (parameterPencil H L).map ψ=H.map φ + C a*L.map φ := by
    rw [parameterPencil,Polynomial.map_add,Polynomial.map_mul,Polynomial.map_C,
      Polynomial.map_map,Polynomial.map_map,hc]
    simp [ψ]
  have hF' : (F.map (C : R →+* R[X])).map ψ=F.map φ := by rw [Polynomial.map_map,hc]
  change ψ ((F.map (C : R →+* R[X])).resultant (parameterPencil H L) m n)=0
  rw [←resultant_map_map,hF',hP']
  apply resultant_zero_of_common_eval (natDegree_map_le.trans hm) _ hp hF hP
  exact (natDegree_add_le _ _).trans (max_le (natDegree_map_le.trans hH)
    ((natDegree_C_mul_le _ _).trans (natDegree_map_le.trans hL)))

end RKCert.FixedPolynomial
