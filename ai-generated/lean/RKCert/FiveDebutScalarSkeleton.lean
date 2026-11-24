module

public import RKCert.FiveDebutScalarCalculus

@[expose] public section

/-! # Four-site characteristic-zero skeleton of the five-debut cut -/
namespace RKCert.FiveDebut
open Polynomial RKCert.Endpoint
open scoped Classical
noncomputable section

variable {K : Type*} [Field K] [CharZero K]

private theorem fourth_leading {V A : K[X]} (dV : V.natDegree=4) (dA : A.natDegree≤1)
    (B : K) (h : shiftedPrimitive V=A*V.derivative+C B*V) :
    (4:K)*A.coeff 1+B=1/6 := by
  have hn : V.coeff 4≠0 := by
    have hV : V≠0 := fun e => by rw [e,natDegree_zero] at dV; omega
    rw [←dV,coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hV
  have dV' : V.derivative.natDegree≤3 := by rw [natDegree_derivative,dV]
  have e := congrArg (fun q : K[X] => q.coeff 4) h
  rw [coeff_shiftedPrimitive,coeff_add,coeff_affine_mul_top A V.derivative dA dV',
    coeff_C_mul,coeff_derivative] at e
  norm_num at e
  apply mul_right_cancel₀ hn
  linear_combination -e

private theorem affine_proportional_from_zero {A D : K[X]}
    (dA : A.natDegree≤1) (dD : D.natDegree≤1) {r : K}
    (hA : A.coeff 1≠0) (a0 : A.eval r=0) (d0 : D.eval r=0) :
    ∃ t : K,D=C t*A := by
  let t := D.coeff 1/A.coeff 1
  have h1 : t*A.coeff 1=D.coeff 1 := div_mul_cancel₀ _ hA
  rw [affine_eval dA] at a0
  rw [affine_eval dD] at d0
  have h0 : t*A.coeff 0=D.coeff 0 := by
    linear_combination t*a0 - d0 - r*h1
  refine ⟨t,?_⟩
  calc
    D = C (D.coeff 1)*X+C (D.coeff 0) := eq_X_add_C_of_natDegree_le_one dD
    _ = C t*(C (A.coeff 1)*X+C (A.coeff 0)) := by
      rw [←h1,←h0,map_mul,map_mul]; ring
    _ = C t*A := by rw [←eq_X_add_C_of_natDegree_le_one dA]

omit [CharZero K] in
private theorem center_affine (u : K) {D : K[X]} (dD : D.natDegree≤1) :
    D-(X-C u)*D.derivative=C (D.eval u) := by
  rw [affine_eval dD,derivative_affine dD,map_add,map_mul]
  conv_lhs => lhs; rw [eq_X_add_C_of_natDegree_le_one dD]
  ring

set_option maxHeartbeats 650000 in
/-- The four paid slopes determine the first primitive exactly. The
fourth knot may be anywhere nonzero in the field; no dilation or ordering
of the coefficients is needed. -/
theorem four_knot_skeleton {U V A D E : K[X]} (u : K) (un : u≠0)
    (hV : V=(X-C u)*U) (dU : U.natDegree=3) (Uu : U.eval u≠0)
    (V0 : V.eval 0≠0) (z : Fin 3→K) (inj : Function.Injective z)
    (zn : ∀ i,z i≠0) (zu : ∀ i,U.eval (z i)=0) (zdu : ∀ i,U.derivative.eval (z i)≠0)
    (dA : A.natDegree≤1) (dD : D.natDegree≤1) (dE : E.natDegree≤1)
    (B : K) (h₄ : shiftedPrimitive V=A*V.derivative+C B*V)
    (h₃ : shiftedPrimitive U=((X-C u)*D)*U.derivative+E*U) :
    shiftedPrimitive V=C (1/18:K)*(X-C u)*V.derivative-C (1/18:K)*V := by
  let Z : K[X] := X-C u
  let k : K := A.coeff 1+B
  change V=Z*U at hV
  change shiftedPrimitive U=(Z*D)*U.derivative+E*U at h₃
  have dZ : Z.natDegree=1 := natDegree_X_sub_C u
  have zne : Z≠0 := (monic_X_sub_C u).ne_zero
  have Z' : Z.derivative=1 := by simp [Z]
  have une : U≠0 := fun e => by rw [e,natDegree_zero] at dU; omega
  have dV : V.natDegree=4 := by rw [hV,natDegree_mul zne une,dZ,dU]
  have lead := fourth_leading dV dA B h₄
  have ane : A≠0 := by
    intro a0
    have b6 : B=1/6 := by simpa only [a0,coeff_zero,mul_zero,zero_add] using lead
    have v0 : V.coeff 0≠0 := by rwa [coeff_zero_eq_eval_zero]
    have e := congrArg (fun p : K[X] => p.coeff 0) h₄
    rw [a0,zero_mul,zero_add,coeff_shiftedPrimitive,coeff_C_mul,b6] at e
    norm_num at e
    apply v0
    linear_combination 3*e
  have dV1 : V.derivative=Z*U.derivative+U := by rw [hV,derivative_mul,Z',one_mul,add_comm]
  have dV2 : V.derivative.derivative=Z*U.derivative.derivative+C 2*U.derivative := by
    rw [dV1,derivative_add,derivative_mul,Z',one_mul,map_ofNat]
    ring
  have evV :
      X*A*V.derivative.derivative+(C 2*A+X*C k)*V.derivative+(C 2*C B-1)*V=0 := by
    have h := euler_of_shifted V A (C B) h₄
    simpa only [derivative_affine dA,derivative_C,mul_zero,zero_add,k,map_add] using h
  have evU :
      X*(Z*D)*U.derivative.derivative+(C 2*(Z*D)+X*(D+Z*D.derivative+E))*U.derivative+
        (X*E.derivative+C 2*E-1)*U=0 := by
    have h := euler_of_shifted U (Z*D) E h₃
    simpa only [derivative_mul,Z',one_mul] using h
  let G := A*(Z*D.derivative-D+E)-C k*Z*D
  have gdeg : G.natDegree≤2 := by
    have dD' : D.derivative.natDegree≤0 := (natDegree_derivative_le _).trans
      (by omega : D.natDegree-1≤0)
    have d1 : (Z*D.derivative).natDegree≤1 := natDegree_mul_le.trans (by omega)
    have dleft : (Z*D.derivative-D+E).natDegree≤1 := (natDegree_add_le _ _).trans
      (max_le ((natDegree_sub_le _ _).trans (max_le d1 dD)) dE)
    have m1 : (A*(Z*D.derivative-D+E)).natDegree≤2 :=
      natDegree_mul_le.trans (by omega)
    have m2 : (C k*Z*D).natDegree≤2 := natDegree_mul_le.trans (by
      have h := natDegree_C_mul_le k Z
      omega)
    exact (natDegree_sub_le _ _).trans (max_le m1 m2)
  have gz (i : Fin 3) : G.eval (z i)=0 := by
    have v := congrArg (Polynomial.eval (z i)) evV
    have a := congrArg (Polynomial.eval (z i)) evU
    rw [dV2,dV1,hV] at v
    simp only [Z,eval_add,eval_sub,eval_mul,eval_X,eval_C,eval_one,eval_zero,
      zu i,mul_zero,add_zero] at v a
    have e : z i*U.derivative.eval (z i)*G.eval (z i)=0 := by
      simp only [G,Z,eval_add,eval_sub,eval_mul,eval_C,eval_X]
      linear_combination A.eval (z i)*a-D.eval (z i)*v
    exact (mul_eq_zero.mp e).resolve_left (mul_ne_zero (zn i) (zdu i))
  have g0 := eq_of_three_zeros z inj G gdeg gz
  have ke : k=0 := by
    by_contra kn
    have au : A.eval u≠0 := by
      intro az
      have e := congrArg (Polynomial.eval u) evV
      rw [dV1,hV] at e
      simp only [Z,eval_add,eval_sub,eval_mul,eval_X,eval_C,eval_one,eval_zero,
        sub_self,zero_mul,az,mul_zero,zero_add,add_zero] at e
      exact mul_ne_zero (mul_ne_zero un kn) Uu e
    have prop : ∃ t : K,D=C t*A := by
      by_cases a1 : A.coeff 1=0
      · have Ac : A=C (A.coeff 0) := affine_eq_C_of_coeff_one_zero dA a1
        have a0 : A.coeff 0≠0 := fun e => ane (by rw [Ac,e,map_zero])
        have d1 : D.coeff 1=0 := by
          by_contra h1
          have dd := (affine_natDegree_eq_one dD).mp h1
          have de : D≠0 := fun h => h1 (by rw [h,coeff_zero])
          have e : A*(Z*D.derivative-D+E)=C k*(Z*D) := by
            change A*(Z*D.derivative-D+E)-C k*Z*D=0 at g0
            rw [←mul_assoc]
            exact sub_eq_zero.mp g0
          have ldeg : (A*(Z*D.derivative-D+E)).natDegree≤1 := by
            rw [Ac]
            refine (natDegree_C_mul_le _ _).trans ((natDegree_add_le _ _).trans
              (max_le ((natDegree_sub_le _ _).trans (max_le ?_ dD)) dE))
            rw [derivative_affine dD]
            exact natDegree_mul_le.trans (by rw [dZ,natDegree_C])
          rw [e,natDegree_C_mul kn,natDegree_mul zne de,dZ,dd] at ldeg
          omega
        refine ⟨D.coeff 0/A.coeff 0,?_⟩
        calc
          D=C (D.coeff 0) := affine_eq_C_of_coeff_one_zero dD d1
          _=C (D.coeff 0/A.coeff 0)*C (A.coeff 0) := by rw [←map_mul,div_mul_cancel₀ _ a0]
          _=C (D.coeff 0/A.coeff 0)*A := congrArg (C (D.coeff 0/A.coeff 0)*·) Ac.symm
      · let r := -A.coeff 0/A.coeff 1
        have ar : A.eval r=0 := by
          rw [affine_eval dA]
          dsimp [r]
          field_simp
          ring
        have ru : r≠u := fun e => au (e ▸ ar)
        have d0 : D.eval r=0 := by
          have e := congrArg (Polynomial.eval r) g0
          simp only [G,Z,eval_add,eval_sub,eval_mul,eval_X,eval_C,eval_zero,ar,zero_mul,zero_sub,
            neg_eq_zero] at e
          exact (mul_eq_zero.mp e).resolve_left (mul_ne_zero kn (sub_ne_zero.mpr ru))
        exact affine_proportional_from_zero dA dD a1 ar d0
    obtain ⟨t,dt⟩ := prop
    have hE : E=C t*(A+C B*Z) := by
      have hf : G=A*(E-C t*(A+C B*Z)) := by
        change A*(Z*D.derivative-D+E)-C k*Z*D=_
        rw [dt,derivative_mul,derivative_C,zero_mul,zero_add,derivative_affine dA,
          show C k=C (A.coeff 1)+C B by simp [k]]
        ring
      rw [hf] at g0
      exact sub_eq_zero.mp ((mul_eq_zero.mp g0).resolve_left ane)
    have comp : shiftedPrimitive U=C t*shiftedPrimitive V := by
      rw [h₃,h₄,dt,hE,dV1,hV]
      ring
    have tn : t≠0 := fun e => shiftedPrimitive_ne_zero une (by rw [comp,e,map_zero,zero_mul])
    have de := congrArg natDegree comp
    rw [shiftedPrimitive_degree,natDegree_C_mul tn,shiftedPrimitive_degree,dU,dV] at de
    omega
  have gE : E=C (D.eval u) := by
    have h : Z*D.derivative-D+E=0 := by
      change A*(Z*D.derivative-D+E)-C k*Z*D=0 at g0
      rw [ke,map_zero,zero_mul,zero_mul,sub_zero] at g0
      exact (mul_eq_zero.mp g0).resolve_left ane
    have e := center_affine u dD
    change D-Z*D.derivative=C (D.eval u) at e
    linear_combination h+e
  have Du : D.coeff 1=0 := by
    by_contra dn
    have d : D.natDegree=1 := (affine_natDegree_eq_one dD).mp dn
    have dne : D≠0 := fun e => dn (by rw [e,coeff_zero])
    have dU' : U.derivative.natDegree=2 := by rw [natDegree_derivative,dU]
    have du' : U.derivative≠0 := fun e => by rw [e,natDegree_zero] at dU'; omega
    have a : ((Z*D)*U.derivative).natDegree=4 := by
      rw [natDegree_mul (mul_ne_zero zne dne) du',natDegree_mul zne dne,dZ,d,dU']
    have c : (E*U).natDegree≤3 := by rw [gE]; exact (natDegree_C_mul_le _ _).trans_eq dU
    have b := congrArg natDegree h₃
    rw [shiftedPrimitive_degree,dU,natDegree_add_eq_left_of_natDegree_lt (by omega),a] at b
    omega
  let t := D.coeff 0
  have Dc : D=C t := affine_eq_C_of_coeff_one_zero dD Du
  have Ec : E=C t := by rw [gE,Dc,eval_C]
  have hL : shiftedPrimitive U=C t*V.derivative := by rw [h₃,Dc,Ec,dV1]; ring
  have hEuler : U=C t*eulerTwo V.derivative := by
    rw [←eulerTwo_shifted U,hL,eulerTwo,derivative_mul,derivative_C,zero_mul,zero_add,eulerTwo]
    ring
  have hA : A*eulerTwo V.derivative=(1-C 2*C B)*V := by
    rw [ke,map_zero,mul_zero,add_zero] at evV
    rw [eulerTwo]
    linear_combination evV
  have aform : A=C ((1-2*B)*t)*Z := by
    apply mul_right_cancel₀ une
    have hc : C ((1-2*B)*t)=(1-C 2*C B)*C t := by
      rw [map_mul,map_sub,map_one,map_mul]
    rw [hc]
    calc
      A*U = C t*(A*eulerTwo V.derivative) := by rw [hEuler]; ring
      _ = _ := by rw [hA,hV]; ring
  have aslope : A.coeff 1=(1-2*B)*t := by
    have e := congrArg (fun p : K[X] => p.coeff 1) aform
    have oneZ : Z.coeff 1=1 := by norm_num [Z,coeff_sub,coeff_X,coeff_C]
    rw [coeff_C_mul,oneZ,mul_one] at e
    exact e
  have ax : A.coeff 1=1/18 := by
    change A.coeff 1+B=0 at ke
    linear_combination (lead-ke)/3
  have bx : B= -(1/18:K) := by
    dsimp only [k] at ke
    linear_combination ke-ax
  rw [h₄,aform,←aslope,ax,bx,map_neg]
  ring

end
end RKCert.FiveDebut
