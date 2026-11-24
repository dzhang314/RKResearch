module
public import RKCert.RadauPhysicalNondivisibility
public import Mathlib.RingTheory.Coprime.Lemmas

@[expose] public section
namespace RKCert.FixedFactor
open Polynomial RKCert.Paired RKCert.Endpoint
variable {K : Type*} [Field K]

/-- At the interpolation degree exactly equal to the number of sites the
vanishing kernel is the line of multiples of their monic nodal hull. -/
theorem scalar_hull_of_roots [Infinite K] (S : Finset K) (T : K[X])
    (hd : T.natDegree≤S.card) (roots : ∀x∈S, T.eval x=0) : ∃ a:K, T=C a*nodalHull S := by
  classical
  obtain ⟨z,hz⟩:=Infinite.exists_notMem_finset S
  let a:=T.eval z/(nodalHull S).eval z
  have hs : (nodalHull S).eval z≠0:=nodalHull_eval_ne_zero_of_notMem hz
  have dc := (natDegree_C_mul_le a (nodalHull S)).trans (natDegree_nodalHull S).le
  refine ⟨a,Polynomial.eq_of_natDegree_lt_card_of_eval_eq' _ _ (insert z S) ?_ ?_⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl|h
    · rw [eval_mul,eval_C,div_mul_cancel₀ _ hs]
    · rw [roots x h,eval_mul,nodalHull_eval_of_mem h,mul_zero]
  · rw [Finset.card_insert_of_notMem hz]; omega

/-- With seven distinct off sites and a quadratic-or-lower head P nonzero
there, all of Q and XQ cannot be represented on those sites by P times
degree-five polynomials unless P divides Q. The two constant interpolation
remainders would force P to divide a linear polynomial. -/
theorem seven_off_pair_obstruction [Infinite K] (S : Finset K) (N : S.card=7)
    (P Q : K[X]) (dP : P.natDegree≤2) (dQ : Q.natDegree≤5) (nondiv : ¬ P∣Q)
    (pn : ∀x∈S, P.eval x≠0) (T U : K[X]) (dT:T.natDegree≤5) (dU:U.natDegree≤5)
    (atQ : ∀x∈S, Q.eval x=P.eval x*T.eval x)
    (atXQ: ∀x∈S, (X*Q).eval x=P.eval x*U.eval x) : False := by
  classical
  let H:=nodalHull S
  have hH : H.natDegree=7 := (natDegree_nodalHull S).trans N
  have hc : IsCoprime P H := by
    unfold H nodalHull
    apply IsCoprime.prod_right
    intro x hx
    exact ((irreducible_X_sub_C x).coprime_iff_not_dvd.mpr
      (fun h=>pn x hx (dvd_iff_isRoot.mp h))).symm
  have hX : (X*Q).natDegree≤6:=natDegree_mul_le_of_le (by simp) dQ
  have pq := natDegree_mul_le_of_le dP dT
  have pu := natDegree_mul_le_of_le dP dU
  obtain ⟨a,ea⟩:=scalar_hull_of_roots S (Q-P*T)
    ((natDegree_sub_le_of_le dQ pq).trans (by omega)) (fun x hx=>by rw [eval_sub,eval_mul,atQ x hx,sub_self])
  obtain ⟨b,eb⟩:=scalar_hull_of_roots S (X*Q-P*U)
    ((natDegree_sub_le_of_le hX pu).trans (by omega)) (fun x hx=>by rw [eval_sub,atXQ x hx,eval_mul,sub_self])
  change Q-P*T=C a*H at ea
  change X*Q-P*U=C b*H at eb
  have an : a≠0 := by
    intro e
    rw [e,map_zero,zero_mul] at ea
    exact nondiv ⟨T,sub_eq_zero.mp ea⟩
  have tot : (Q-P*T).natDegree=7 := by rw [ea,natDegree_C_mul an,hH]
  have dP2 : P.natDegree=2 := by
    by_contra! n
    have hmul : (P*T).natDegree≤6 := (natDegree_mul_le ..).trans (by omega)
    have hsub : (Q-P*T).natDegree≤6 := natDegree_sub_le_of_le dQ hmul
    omega
  let V : K[X]:=C a*X-C b
  have dv : P∣V*H := by
    refine ⟨U-X*T,?_⟩
    dsimp only [V]
    linear_combination -X*ea + eb
  have dV:=hc.dvd_of_dvd_mul_right dv
  have vn: V≠0 := by
    intro e
    have t:=congrArg (fun W:K[X]=>W.coeff 1) e
    apply an
    simpa [V,coeff_C_mul,coeff_C] using t
  have hdV : V.natDegree≤1 :=
    natDegree_sub_le_of_le ((natDegree_C_mul_le a (X:K[X])).trans (natDegree_X (R:=K)).le) (show (C b).natDegree≤0 by simp)
  have too:=natDegree_le_of_dvd dV vn
  omega

end RKCert.FixedFactor
