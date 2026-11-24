module

public import RKCert.ERKLowEarlyPrimitive

@[expose] public section

/-! # Exact early polynomial-kernel and four-off residue tests -/
namespace RKCert.Paired
open Module Polynomial RKCert.Endpoint
open scoped Classical
variable {K : Type*} [Field K] [CharZero K] {s : ℕ}

omit [CharZero K] in
/-- A six-dimensional grade-three coefficient domain with two literal
off receivers in five rows has a nonzero polynomial component in
some null vector, not just a nonzero arbitrary profile. -/
theorem degree_three_kernel_on_five_rows {A : Fin s→Fin s→K} (e : Fin 5→Fin s)
    {i j : Fin 5} (gi : qdef A (e i)≠0) (gj : qdef A (e j)≠0)
    (ne : nodes A (e i)≠nodes A (e j)) :
    ∃ Q R : K[X], Q≠0 ∧ Q.natDegree≤3 ∧ R.natDegree≤1 ∧
      ∀ k : Fin 5, (evalNodes A Q+diag (qdef A) (evalNodes A R)) (e k)=0 := by
  let f : ((Fin 4→K)×(Fin 2→K)) →ₗ[K] Vec K 5 :=
    (restrictCol e).comp ((polyEval A 3).coprod ((diag (qdef A)).comp (polyEval A 1)))
  have hI : ¬Function.Injective f := by
    intro h
    have dim := LinearMap.finrank_le_finrank_of_injective h
    norm_num [Module.finrank_prod,Module.finrank_fin_fun,Vec] at dim
  have nn : ¬ ∀z, f z=0 → z=0 := fun he =>
    hI ((injective_iff_map_eq_zero f).mpr he)
  push Not at nn
  obtain ⟨z,hz,zn⟩ := nn
  let Q := ofFn 4 z.1
  let R := ofFn 2 z.2
  have dQ : Q.natDegree≤3 := Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) _)
  have dR : R.natDegree≤1 := Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) _)
  have vv (k : Fin 5) : (evalNodes A Q+diag (qdef A) (evalNodes A R)) (e k)=0 := by
    have h := congrFun hz k
    rw [evalNodes_ofFn A 3,evalNodes_ofFn A 1]
    exact h
  refine ⟨Q,R,?_,dQ,dR,vv⟩
  intro q0
  have h1 : R.eval (nodes A (e i))=0 := (mul_eq_zero.mp (by simpa [q0] using vv i)).resolve_left gi
  have h2 : R.eval (nodes A (e j))=0 := (mul_eq_zero.mp (by simpa [q0] using vv j)).resolve_left gj
  have r0 : R=0 := eq_zero_of_natDegree_lt_card_of_eval_eq_zero' R
    ({nodes A (e i),nodes A (e j)} : Finset K) (fun x hx => by
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl|rfl <;> assumption) (by rw [Finset.card_pair ne]; omega)
  exact zn (Prod.ext (injective_ofFn 4 (q0.trans (ofFn_zero _).symm))
    (injective_ofFn 2 (r0.trans (ofFn_zero _).symm)))

/-- At four genuine off roots, the chronological null vector's
primitive is nontrivially congruent to their quartic hull. -/
theorem four_off_residue_of_paid_primitive {A : Fin s→Fin s→K}
    (hF : zeroSpace A 4=chainSpan A (qdef A) 2) {P : K[X]} (dP : P.natDegree≤2)
    (fit : ∀ i,qdef A i≠0 → P.eval (nodes A i)=qdef A i)
    (Q R : K[X]) (dQ : Q.natDegree≤3) (dR : R.natDegree≤1)
    (n : ¬P∣primitive Q) (S : Finset K) (card : S.card=4)
    (off : ∀ x∈S, ∃ i, qdef A i≠0 ∧ nodes A i=x ∧
      mat A (evalNodes A Q+diag (qdef A) (evalNodes A R)) i=0) :
    ∃ a : K,a≠0 ∧ P∣primitive Q-C a*nodalHull S := by
  obtain ⟨T,dT,h⟩ := degree_three_actual_mat_profile hF Q R dQ dR
  have dq : (primitive Q).natDegree≤4 := primitive_natDegree_le dQ
  have dt : (P*T).natDegree≤4 := by have e := natDegree_mul_le_of_le dP dT; exact e
  obtain ⟨a,ea⟩ := polynomial_scalar_hull S (primitive Q+P*T)
    ((natDegree_add_le_of_degree_le dq dt).trans_eq card.symm) (fun x hx=>by
      obtain ⟨i,g,rfl,z⟩ := off x hx
      rw [profile_off_eval h.symm fit g]
      exact z)
  have an : a≠0 := by
    intro z
    rw [z,map_zero,zero_mul] at ea
    exact n ⟨-T,by rw [mul_neg,eq_neg_iff_add_eq_zero]; exact ea⟩
  exact ⟨a,an,⟨-T,by linear_combination ea⟩⟩

omit [CharZero K] in
theorem positive_degree_head_not_dvd_double_square {P : K[X]} {h a : K}
    (dp : 0<P.natDegree) (a0 : a≠0) (h0 : P.eval 0≠0) (hh : P.eval h≠0) :
    ¬P∣C a*(X^2*(X-C h)^2) := by
  have cp0 : IsCoprime P (X:K[X]) := (irreducible_X.coprime_iff_not_dvd.mpr
    (fun e=>h0 ((coeff_zero_eq_eval_zero P).symm.trans (X_dvd_iff.mp e)))).symm
  have cph : IsCoprime P (X-C h) := ((irreducible_X_sub_C h).coprime_iff_not_dvd.mpr
    (fun e=>hh (dvd_iff_isRoot.mp e))).symm
  have cc : IsCoprime P (C a*(X^2*(X-C h)^2)) :=
    (isCoprime_mul_unit_left_right (isUnit_C.mpr a0.isUnit) _ _).mpr
      ((cp0.pow_right (n:=2)).mul_right (cph.pow_right (n:=2)))
  intro div
  exact (Nat.ne_of_gt dp) (natDegree_eq_zero_of_isUnit (cc.isUnit_of_dvd div))

end RKCert.Paired
