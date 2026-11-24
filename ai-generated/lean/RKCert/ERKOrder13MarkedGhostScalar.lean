module
public import RKCert.ERKOrder13MarkedJacobi
public import RKCert.PolynomialFeatureCapacity

@[expose] public section
/-! # Exact early marked mesh/ghost separation and feature capacity
The degree-six pencil cannot be a polynomial square: its leading and
midpoint coefficients have opposite signs independently of its free
parameter. No real-root enumeration or square-free-pencil assumption
is needed for the degree-six branch.
-/
namespace RKCert.Paired.FiniteMidpoint
open Polynomial RKCert.OrderTwelve
variable {K:Type*} [Field K] [CharZero K]
set_option maxHeartbeats 3300000

omit [CharZero K] in
private theorem coprime_C_add {P Q T:K[X]} {a:K} (an:a≠0)
    (h:IsCoprime P Q) : IsCoprime (C a*P+T*Q) Q := by
  obtain ⟨u,v,e⟩:=h
  have ea : C a⁻¹*C a=(1:K[X]) := by rw [←map_mul,inv_mul_cancel₀ an,map_one]
  refine ⟨u*C a⁻¹,v-u*C a⁻¹*T,?_⟩
  linear_combination e + u*P*ea

private theorem adjacent_d5_d4 : IsCoprime (dFivePoly:K[X]) markD4 := by
  rw [mark_d5_recurrence]
  exact coprime_C_add (by norm_num) mark_d3_d4_coprime

private theorem adjacent_d6_d5 : IsCoprime (dSixPoly:K[X]) dFivePoly := by
  rw [mark_d6_recurrence]
  exact coprime_C_add (by norm_num) (adjacent_d5_d4 (K:=K)).symm

omit [CharZero K] in
private theorem coprime_linear_eval {P:K[X]} {z:K} (h:P.eval z≠0) :
    IsCoprime P (X-C z) := by
  obtain ⟨Q,eq⟩ : X-C z∣P-C (P.eval z) := dvd_iff_isRoot.mpr (by simp)
  have ea : C (P.eval z)⁻¹*C (P.eval z)=(1:K[X]) := by rw [←map_mul,inv_mul_cancel₀ h,map_one]
  refine ⟨C (P.eval z)⁻¹,-C (P.eval z)⁻¹*Q,?_⟩
  linear_combination C (P.eval z)⁻¹*eq + ea

omit [CharZero K] in
private theorem coprime_from_elimination {P H T:K[X]} {a b e:K} (en:e≠0)
    (fit:C a*P+C b*H=C e*T) (h:IsCoprime P T) : IsCoprime P H := by
  obtain ⟨u,v,hu⟩:=h
  have eqT : T=C e⁻¹*(C a*P+C b*H) := by
    rw [fit,←mul_assoc,←map_mul,inv_mul_cancel₀ en,map_one,one_mul]
  refine ⟨u+v*C e⁻¹*C a,v*C e⁻¹*C b,?_⟩
  rw [eqT] at hu
  linear_combination hu

theorem marked_noalias_early_coprime (a b c d ρ:K) (an:a≠0) (hn:c≠0∨d≠0)
    (mg:a/56+b/42=ρ*(a+b)) (mh:c/42+d/30=ρ*(c+d)) :
    IsCoprime (C a*dSixPoly+C b*dFivePoly) (C c*dFivePoly+C d*markD4) := by
  let P:=C a*dSixPoly+C b*dFivePoly
  let H:=C c*dFivePoly+C d*markD4
  have relation : 5*a*c+(13*a+8*b)*d=0 := by
    linear_combination -840*((c+d)*mg-(a+b)*mh)
  have dn : d≠0 := by
    intro h
    rw [h,mul_zero,add_zero] at relation
    have ac : a*c=0 := by linear_combination relation/5
    rcases hn with cn|dn
    · exact (mul_ne_zero an cn) ac
    · exact dn h
  have p1 : P.eval 1≠0 := by
    have e:P.eval 1=a+b := by simp [P,dSixValue,dFive];ring
    rw [e]
    intro h
    rw [h,mul_zero] at mg
    apply an
    linear_combination -168*mg+4*h
  have c1:= (coprime_linear_eval p1).mul_right
    (coprime_C_add (T:=C b) an (adjacent_d6_d5 (K:=K)))
  apply coprime_from_elimination (a:=d) (b:=(5:K)/8*a) (e:=(13:K)/4*a*d)
    (mul_ne_zero (mul_ne_zero (by norm_num) an) dn) _ c1
  apply @Polynomial.funext K _ _ (Infinite.of_injective (fun n:ℕ=>(n:K)) Nat.cast_injective)
  intro x
  unfold P
  rw [mark_d6_recurrence]
  simp only [eval_add,eval_mul,eval_C,eval_sub,eval_X]
  linear_combination ((dFivePoly:K[X]).eval x/8)*relation

theorem marked_alias_early_coprime (b c d ρ:K) (bn:b≠0) (hn:c≠0∨d≠0)
    (mg:b/42=ρ*b) (mh:c/30+d/20=ρ*(c+d)) :
    IsCoprime (C b*dFivePoly) (C c*markD4+C d*markD3) := by
  let P:=C b*(dFivePoly:K[X])
  let H:=C c*markD4+C d*markD3
  have rho:ρ=1/42 := by
    apply mul_right_cancel₀ bn
    linear_combination -mg
  rw [rho] at mh
  have relation : 4*c+11*d=0 := by linear_combination 420*mh
  have dn:d≠0 := by
    intro h
    rw [h,mul_zero,add_zero] at relation
    have c0:c=0 := by linear_combination relation/4
    exact (hn.elim (fun n=>n c0) (fun n=>n h))
  have p1 : P.eval 1≠0 := by
    have e:P.eval 1=b := by norm_num [P,dFive]
    rwa [e]
  have kin : IsCoprime P markD4 := by
    simpa only [P,zero_mul,add_zero] using
      coprime_C_add (T:=(0:K[X])) bn (adjacent_d5_d4 (K:=K))
  have co:= (coprime_linear_eval p1).mul_right kin
  apply coprime_from_elimination (a:=d) (b:=(4:K)/7*b) (e:=(22:K)/7*b*d)
    (mul_ne_zero (mul_ne_zero (by norm_num) bn) dn) _ co
  apply @Polynomial.funext K _ _ (Infinite.of_injective (fun n:ℕ=>(n:K)) Nat.cast_injective)
  intro x
  unfold P
  rw [mark_d5_recurrence]
  simp only [eval_add,eval_mul,eval_C,eval_sub,eval_X]
  linear_combination ((markD4:K[X]).eval x * b/7)*relation

theorem marked_noalias_degree_leading {a b:K} (an:a≠0) :
    (C a*dSixPoly+C b*dFivePoly:K[X]).natDegree=6 ∧
    (C a*dSixPoly+C b*dFivePoly:K[X]).leadingCoeff=a*429 := by
  have h:=natDegree_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr an) (dSixPoly:K[X])
  rw [dSixPoly_degree] at h
  have l : (C b*dFivePoly:K[X]).natDegree≤5 := by
    simpa only [natDegree_C,natDegree_dFivePoly,zero_add] using
      (natDegree_mul_le (p:=C b) (q:=(dFivePoly:K[X])))
  have lt : (C b*dFivePoly:K[X]).natDegree<(C a*dSixPoly:K[X]).natDegree := by omega
  refine ⟨(natDegree_add_eq_left_of_natDegree_lt lt).trans h,?_⟩
  rw [leadingCoeff_add_of_degree_lt' (degree_lt_degree lt),
    leadingCoeff_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr an),leadingCoeff,dSixPoly_degree]
  have h6 : (dSixPoly:K[X]).coeff 6=429 := by
    have raw:=congrArg (fun P:K[X]=>P.coeff 7) (dx6_as_dSix (K:=K))
    change (dx6:K[X]).coeff 7=(56•(X*dSixPoly):K[X]).coeff (6+1) at raw
    rw [dx6_coeff 7 (by decide),AddMonoidAlgebra.coeff_smul_apply,coeff_X_mul] at raw
    norm_num [nsmul_eq_mul] at raw
    linear_combination -raw/56
  rw [h6]


omit [CharZero K] in
theorem marked_eliminant_capacity (P H Q R :K[X]) (pn:P≠0)
    (co:IsCoprime P H) (qn:Q≠0→¬P∣Q^2)
    (fdeg:(X*P).natDegree≤7) (hdeg:(X*H).natDegree≤6) (qdeg:Q.natDegree≤3)
    (budget:(X*P).natDegree+Q.natDegree+R.natDegree≤14)
    (S:Finset (K×K))
    (hs:∀ w∈S,w.2≠0∧(X*P).eval w.1=w.2*Q.eval w.1∧
      w.2^2=(X*H).eval w.1+w.2*R.eval w.1) :
    S.card≤13 ∧ ∀ x:K,(X*P).eval x=0→(X*H).eval x=0→x=0 := by
  classical
  let F:=X*P
  let D:=X*H
  let Φ:=F^2-F*Q*R-D*Q^2
  have φn:Φ≠0 := by
    intro phi
    by_cases q0:Q=0
    · exact pow_ne_zero 2 (mul_ne_zero X_ne_zero pn) (by simpa [Φ,F,q0] using phi)
    · have he:F^2-F*Q*R=D*Q^2 := sub_eq_zero.mp phi
      have h : X*P^2-P*Q*R=H*Q^2 := by
        apply mul_left_cancel₀ X_ne_zero
        calc X*(X*P^2-P*Q*R)=F^2-F*Q*R := by dsimp [F];ring
          _ = D*Q^2 := he
          _ = X*(H*Q^2) := by dsimp [D];ring
      have ph : P∣H*Q^2 := ⟨X*P-Q*R,by rw [←h];ring⟩
      exact qn q0 (co.dvd_of_dvd_mul_left ph)
  have φDeg : Φ.natDegree≤14 := by
    change (F^2-F*Q*R-D*Q^2).natDegree≤14
    change F.natDegree≤7 at fdeg
    change D.natDegree≤6 at hdeg
    change F.natDegree+Q.natDegree+R.natDegree≤14 at budget
    apply le_trans (natDegree_sub_le _ _) (max_le ?_ ?_)
    · apply le_trans (natDegree_sub_le _ _) (max_le ?_ ?_)
      · rw [natDegree_pow];omega
      · have u:=natDegree_mul_le (p:=F*Q) (q:=R)
        have v:=natDegree_mul_le (p:=F) (q:=Q)
        omega
    · have u:=natDegree_mul_le (p:=D) (q:=Q^2)
      rw [natDegree_pow] at u
      omega
  have bound:=RKCert.Paired.FeatureCapacity.count_by_eliminant S F D Q R (by simp [F]) (by simp [D]) φn hs
  change S.card+1≤Φ.natDegree at bound
  refine ⟨by omega,?_⟩
  intro x hp hh
  by_contra nx
  have xP : P.eval x=0 := (mul_eq_zero.mp (by simpa only [eval_mul,eval_X] using hp)).resolve_left nx
  have xH : H.eval x=0 := (mul_eq_zero.mp (by simpa only [eval_mul,eval_X] using hh)).resolve_left nx
  obtain ⟨u,v,h⟩:=co
  have raw:=congrArg (fun P:K[X]=>P.eval x) h
  simp only [eval_add,eval_mul,xP,xH,mul_zero,add_zero,eval_one] at raw
  exact zero_ne_one raw

section Ordered
variable [LinearOrder K] [IsStrictOrderedRing K]
omit [CharZero K] in
theorem marked_noalias_pencil_not_square_divisor {a b:K} (an:a≠0) {Q:K[X]}
    (qne:Q≠0) (qd:Q.natDegree≤3) :
    ¬(C a*dSixPoly+C b*dFivePoly:K[X])∣Q^2 := by
  let P:K[X]:=C a*dSixPoly+C b*dFivePoly
  have e := marked_noalias_degree_leading (a:=a) (b:=b) an
  change P.natDegree=6∧P.leadingCoeff=a*429 at e
  have pn:P≠0 := by intro h;rw [h,natDegree_zero] at e;omega
  rintro ⟨R,fit⟩
  have rn:R≠0 := fun h=>pow_ne_zero 2 qne (by rw [fit,h,mul_zero])
  have rd : R.natDegree=0 := by
    have h:=congrArg natDegree fit
    change (Q^2).natDegree=(P*R).natDegree at h
    rw [natDegree_pow,natDegree_mul pn rn,e.1] at h
    omega
  let ρ:=R.coeff 0
  have eqR : R=C ρ := eq_C_of_natDegree_eq_zero rd
  rw [eqR] at fit
  have lc := congrArg leadingCoeff fit
  rw [leadingCoeff_pow,leadingCoeff_mul,e.2,leadingCoeff_C] at lc
  have lcpos : 0<Q.leadingCoeff^2 := sq_pos_of_ne_zero (leadingCoeff_ne_zero.mpr qne)
  have sign : 0<a*ρ := by linarith [show Q.leadingCoeff^2=429*(a*ρ) by linear_combination lc]
  have ev := congrArg (fun F:K[X]=>F.eval (1/2)) fit
  have mid : P.eval (1/2)=-(5:K)/64*a := by norm_num [P,dSixValue,dFive];ring
  rw [eval_pow,eval_mul,eval_C,mid] at ev
  have sq := sq_nonneg (Q.eval (1/2))
  have e' : (Q.eval (1/2))^2=-(5:K)/64*(a*ρ) := by linear_combination ev
  linarith

end Ordered
end RKCert.Paired.FiniteMidpoint
