module

public import RKCert.Dirk15SignatureAlgebra

@[expose] public section

/-! # Exact seventeen-signature square identity

Two physical signatures with one clock pay the square of its linear
factor. This is a general polynomial identity, not an assumption that
the original nodes are distinct or that a branch has been eliminated.
-/
namespace RKCert.Paired.Signature
open Polynomial
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] {n : ℕ}

theorem counted_clock_divisors_zero (clock : Fin n → K) {P : K[X]}
    (dp : P.natDegree<n)
    (by_fiber : ∀ a ∈ Finset.univ.image clock, (X-C a)^(fiberAt clock a).card∣P) :
    P=0 := by
  let S := Finset.univ.image clock
  let f := fun a : K => (X-C a)^(fiberAt clock a).card
  have h : (∏ a∈S,f a)∣P := Finset.prod_dvd_of_coprime
    (fun a _ b _ ne => (isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr ne).isUnit).pow)
    by_fiber
  have dg : (∏ a∈S,f a).natDegree=n := by
    rw [natDegree_prod_of_monic S f (fun z _ => (monic_X_sub_C z).pow _)]
    simp only [f,natDegree_pow,natDegree_X_sub_C,mul_one]
    simpa only [S,fiberAt,Finset.card_univ,Fintype.card_fin] using
      (Finset.card_eq_sum_card_image clock (Finset.univ : Finset (Fin n))).symm
  exact eq_zero_of_dvd_of_natDegree_lt h (by rw [dg]; exact dp)

theorem quadratic_signature_fiber (c w : Fin n → K) {s t : K[X]} (α : K)
    (inj : Function.Injective (fun i => (c i,w i)))
    (hq : ∀ i,w i^2=w i*s.eval (c i)+α*t.eval (c i))
    (a : K) : (fiberAt c a).card≤2 := by
  let V := fiberAt c a
  let Q : K[X] := X^2-C (s.eval a)*X-C (α*t.eval a)
  have d : Q.natDegree≤2 := (natDegree_sub_le _ _).trans (max_le
    ((natDegree_sub_le _ _).trans (max_le (by rw [natDegree_X_pow])
      ((natDegree_C_mul_le _ _).trans (by simp)))) (by rw [natDegree_C]; decide))
  have nonzero : Q≠0 := by
    intro e
    have h := congrArg (fun r : K[X] => r.coeff 2) e
    norm_num [Q,coeff_sub,coeff_X_pow,coeff_C_mul,coeff_X,coeff_C] at h
  have injw : Set.InjOn w (V:Set (Fin n)) := by
    intro i hi j hj e
    have c1 : c i=a := (Finset.mem_filter.mp hi).2
    have c2 : c j=a := (Finset.mem_filter.mp hj).2
    exact inj (Prod.ext (c1.trans c2.symm) e)
  have s : (V.image w).val ⊆ Q.roots := by
    intro y hy
    obtain ⟨i,im,rfl⟩ := Finset.mem_image.mp (show y∈V.image w from hy)
    have c1 : c i=a := (Finset.mem_filter.mp im).2
    apply (mem_roots nonzero).mpr
    rw [IsRoot.def]
    simp only [Q,eval_sub,eval_pow,eval_X,eval_mul,eval_C,←c1]
    rw [hq i]
    ring
  have r := Polynomial.card_le_degree_of_subset_roots s
  have b := r.trans d
  rwa [Finset.card_image_of_injOn injw] at b

def squareSignatureExpression (D R T H : K[X]) (scale : K) : K[X] :=
  D^2-D*R*T-C scale*H*R^2

theorem square_signatures_close (c w : Fin n → K) (D R T H : K[X]) (scale : K)
    (dg : (squareSignatureExpression D R T H scale).natDegree<n)
    (inj : Function.Injective (fun i => (c i,w i)))
    (dh : ∀ i,D.eval (c i)=w i*R.eval (c i))
    (quad : ∀ i,w i^2=w i*T.eval (c i)+scale*H.eval (c i)) :
    squareSignatureExpression D R T H scale=0 := by
  let P := squareSignatureExpression D R T H scale
  have zero_at (i : Fin n) : P.eval (c i)=0 := by
    simp only [P,squareSignatureExpression,eval_sub,eval_pow,eval_mul,eval_C,dh]
    linear_combination (R.eval (c i))^2 * quad i
  apply counted_clock_divisors_zero c dg
  intro a ha
  obtain ⟨i,_,ai⟩ := Finset.mem_image.mp ha
  have im : i∈fiberAt c a := by simp [fiberAt,ai]
  have pos : 0 < (fiberAt c a).card := Finset.card_pos.mpr ⟨i,im⟩
  have cap := quadratic_signature_fiber c w scale inj quad a
  rcases (show (fiberAt c a).card=1 ∨ (fiberAt c a).card=2 by omega) with k|k
  · rw [k,pow_one]
    exact dvd_iff_isRoot.mpr (ai ▸ zero_at i)
  · have exists_other : ∃j∈fiberAt c a,j≠i := by
      by_contra! no
      have hs : fiberAt c a⊆{i} := fun j hj => Finset.mem_singleton.mpr (no j hj)
      have p := Finset.card_le_card hs
      rw [k,Finset.card_singleton] at p
      omega
    obtain ⟨j,jm,jn⟩ := exists_other
    have aj : c j=a := (Finset.mem_filter.mp jm).2
    have wne : w j≠w i := fun e => jn (inj (Prod.ext (aj.trans ai.symm) e))
    have di := dh i
    have dj := dh j
    rw [ai] at di
    rw [aj] at dj
    have rzero : R.eval a=0 := by
      have mul : (w j-w i)*R.eval a=0 := by rw [sub_mul,←di,←dj,sub_self]
      exact (mul_eq_zero.mp mul).resolve_left (sub_ne_zero.mpr wne)
    have dzero : D.eval a=0 := by rw [di,rzero,mul_zero]
    have xd : X-C a∣D := dvd_iff_isRoot.mpr dzero
    have xr : X-C a∣R := dvd_iff_isRoot.mpr rzero
    rw [k]
    change (X-C a)^2∣D^2-D*R*T-C scale*H*R^2
    have fr : (X-C a)^2∣R^2 := by simpa only [pow_two] using mul_dvd_mul xr xr
    have fd : (X-C a)^2∣D^2 := by simpa only [pow_two] using mul_dvd_mul xd xd
    have dr : (X-C a)^2∣(D*R)*T := by
      have pr : (X-C a)^2∣D*R := by simpa only [pow_two] using mul_dvd_mul xd xr
      exact pr.mul_right T
    exact (fd.sub dr).sub (fr.mul_left _)

theorem square_signature_degree_bound {D R T H : K[X]} {scale : K}
    (dD : D.natDegree≤8) (dR : R.natDegree≤4) (dT : T.natDegree≤4) (dH : H.natDegree≤8) :
    (squareSignatureExpression D R T H scale).natDegree≤16 := by
  unfold squareSignatureExpression
  have r1 := natDegree_pow D 2
  have r2 := natDegree_pow R 2
  have e := natDegree_mul_le (p:=D) (q:=R)
  have g := natDegree_mul_le (p:=D*R) (q:=T)
  have h := natDegree_C_mul_le scale H
  have m := natDegree_mul_le (p:=C scale*H) (q:=R^2)
  exact (natDegree_sub_le _ _).trans
    (max_le ((natDegree_sub_le _ _).trans (max_le (by omega) (by omega))) (by omega))

end
end RKCert.Paired.Signature
