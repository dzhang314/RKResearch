module
public import RKCert.FiveDebutHankel
@[expose] public section
namespace RKCert.FiveDebut
open Polynomial RKCert.Paired RKCert.FourDebut
variable {K : Type*} [Field K] [CharZero K] {n : ℕ}
noncomputable section

/-- The three-debut cut makes the first signed two-by-two Hankel block singular. -/
theorem three_cut_singular {z w : Fin 3→K} (inj : Function.Injective z)
    (nz : ∀i,z i≠0) (nw : ∀i,w i≠0) {P Q : K[X]} (pn : P≠0)
    (dp : P.natDegree≤5) (p0 : P.eval 0=0) (dq : Q.degree<(1:WithBot ℕ))
    (fit : ∀i,P.eval (z i)=w i*Q.eval (z i)) (zeros : ∀i,(primitive P).eval (z i)=0) :
    let a:=fun i=>z i^2/w i
    sumPower z a 0*sumPower z a 2=(sumPower z a 1)^2 := by
  let a:=fun i=>z i^2/w i
  obtain ⟨G,gn,dg,prod⟩:=double_origin_factor z inj nz (e:=1) pn p0 dp zeros
  have degQ:Q.natDegree+2≤2:=by
    by_cases hn:Q=0
    · simp [hn]
    · have dn:Q.natDegree<1:=(natDegree_lt_iff_degree_lt hn).mpr dq
      omega
  have val (i:Fin 3):Q.eval (z i)=denomin z i*(a i*G.eval (z i)) := by
    apply mul_left_cancel₀ (nw i)
    rw [←fit,derivative_on_old z prod i]
    dsimp [a];field_simp [nw i]
  have both:=barycentric_moment_pair inj degQ val
  exact affine_annihilator gn dg both.1 both.2

/-- The fifth cut gives a nonzero fourth amplitude and both equations of
the fifth-clock kernel of the four-atom Hankel block at once. -/
theorem five_cut_linear_kernel {z w : Fin 4→K} {u : K} (inj : Function.Injective z)
    (nz : ∀i,z i≠0) (nu:u≠0) (fresh : ∀i,u≠z i)
    {P Q : K[X]} (pn : P≠0) (dp : P.natDegree≤6) (p0 : P.eval 0=0) (dq : Q.degree<(2:WithBot ℕ))
    (fit : ∀i,P.eval (z i)=w i*Q.eval (z i)) (zu : (primitive P).eval u=0)
    (zeros : ∀i,(primitive P).eval (z i)=0) :
    let a:=fun i=>z i^2/w i
    (∀i,w i≠0) ∧ sumPower z a 1=u*sumPower z a 0 ∧ sumPower z a 2=u*sumPower z a 1 := by
  let a:=fun i=>z i^2/w i
  let zz : Fin 5→K :=Fin.cons u z
  have injall : Function.Injective zz:= by
    intro i;refine Fin.cases ?_ (fun l=>?_) i
    · intro j;exact Fin.cases (fun _=>rfl) (fun t h=>False.elim (fresh t h)) j
    · intro j;exact Fin.cases (fun h=>False.elim (fresh l h.symm)) (fun t h=>congrArg Fin.succ (inj h)) j
  obtain ⟨b,bn,fac⟩:=double_origin_shape zz injall (Fin.cases nu nz) pn p0 dp (Fin.cases zu zeros)
  have divi : Lagrange.nodal Finset.univ zz=(X-C u)*Lagrange.nodal Finset.univ z := by
    rw [Lagrange.nodal_eq,Fin.prod_univ_succ];simp only [zz,Fin.cons_zero,Fin.cons_succ,Lagrange.nodal_eq]
  rw [divi] at fac
  have prod : primitive P=X^2*Lagrange.nodal Finset.univ z*((X-C u)*C b):=by rw [fac];ring
  have der (i:Fin 4) : P.eval (z i)=z i^2*denomin z i*((z i-u)*b):=by
    simpa only [eval_mul,eval_sub,eval_X,eval_C] using derivative_on_old z prod i
  have nw (i : Fin 4) : w i≠0:=by
    intro no
    have e:=fit i
    rw [der,no,zero_mul] at e
    exact (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (nz i)) (denom_ne_zero inj i))
      (mul_ne_zero (sub_ne_zero.mpr (fresh i).symm) bn)) e
  have dd:Q.natDegree+2≤3:=by
    by_cases h:Q=0
    · simp [h]
    · have h':Q.natDegree<2:=(natDegree_lt_iff_degree_lt h).mpr dq
      omega
  have val (i:Fin 4):Q.eval (z i)=denomin z i*(b*(a i*(z i-u))) := by
    apply mul_left_cancel₀ (nw i);rw [←fit,der];dsimp [a];field_simp [nw i]
  have pair:=barycentric_moment_pair inj dd val
  have e0:(∑i,a i*(z i-u))=0:=by
    have h:=pair.1
    rw [←Finset.mul_sum] at h
    exact (mul_eq_zero.mp h).resolve_left bn
  have e1:(∑i,z i*(a i*(z i-u)))=0:=by
    have h:=pair.2
    simp_rw [show ∀i : Fin 4,z i*(b*(a i*(z i-u)))=b*(z i*(a i*(z i-u))) by intro i;ring] at h
    rw [←Finset.mul_sum] at h
    exact (mul_eq_zero.mp h).resolve_left bn
  refine ⟨nw,sub_eq_zero.mp ?_,sub_eq_zero.mp ?_⟩
  · convert e0 using 1
    simp only [sumPower,Finset.mul_sum,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl;intro i _;ring
  · convert e1 using 1
    simp only [sumPower,Finset.mul_sum,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl;intro i _;ring

omit [CharZero K] in
/-- Adding a nonzero fourth atom with clock z to a singular 2×2 block
cannot give a nonzero block with kernel direction (−u,1) for u≠z. -/
theorem fourth_atom_zero {a b c w z u : K} (det : a*c=b^2) (wn:w≠0) (zu:z≠u)
    (p1:b+w*z=u*(a+w)) (p2:c+w*z^2=u*(b+w*z)) :
    a+w=0 ∧ b+w*z=0 ∧ c+w*z^2=0 := by
  have eb:b=u*(a+w)-w*z:=by linear_combination p1
  have ec:c=u^2*(a+w)-w*z^2:=by linear_combination p2+u*p1
  rw [eb,ec] at det
  have e:w*(z-u)^2*(a+w)=0:=by linear_combination -det
  have v: a+w=0 := (mul_eq_zero.mp e).resolve_left (mul_ne_zero wn (pow_ne_zero _ (sub_ne_zero.mpr zu)))
  exact ⟨v,by rw [p1,v,mul_zero],by rw [p2,p1,v,mul_zero,mul_zero]⟩

end
end RKCert.FiveDebut
