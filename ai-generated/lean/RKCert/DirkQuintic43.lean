module
public import RKCert.EndpointPhysical
public import RKCert.DirkShortTrace
@[expose] public section
namespace RKCert.Endpoint
open Polynomial
variable {K:Type*} [Field K] [CharZero K]
set_option maxHeartbeats 4500000

/-- The 4+3 two-pivot moment rule excludes every quintic over any characteristic-zero field. -/
theorem normalized_four_three (c:Fin 6→K) (a:K) (ha:a≠0) (neq:a≠1)
    (one:∀k:Fin 4,moment c 1 (k.val+1)=0) (two:∀k:Fin 3,moment c a (k.val+2)-moment c a (k.val+1)=0) : c=0 :=by
  have h1:c 0/2+c 1/3+c 2/4+c 3/5+c 4/6+c 5/7=0:=by
    have t:=one (0:Fin 4)
    norm_num [moment,Fin.sum_univ_succ] at t
    convert t using 1; ring
  have h2:c 0/3+c 1/4+c 2/5+c 3/6+c 4/7+c 5/8=0:=by
    have t:=one (1:Fin 4)
    norm_num [moment,Fin.sum_univ_succ] at t
    convert t using 1; ring
  have h3:c 0/4+c 1/5+c 2/6+c 3/7+c 4/8+c 5/9=0:=by
    have t:=one (2:Fin 4)
    norm_num [moment,Fin.sum_univ_succ] at t
    convert t using 1; ring
  have h4:c 0/5+c 1/6+c 2/7+c 3/8+c 4/9+c 5/10=0:=by
    have t:=one (3:Fin 4)
    norm_num [moment,Fin.sum_univ_succ] at t
    convert t using 1; ring
  have c0:c 0=(5/126)*c 4+(2/21)*c 5:=by
    linear_combination (200)*h1+(-1200)*h2+(2100)*h3+(-1120)*h4
  have c1:c 1=(-10/21)*c 4+(-15/14)*c 5:=by
    linear_combination (-1200)*h1+(8100)*h2+(-15120)*h3+(8400)*h4
  have c2:c 2=(5/3)*c 4+(10/3)*c 5:=by
    linear_combination (2100)*h1+(-15120)*h2+(29400)*h3+(-16800)*h4
  have c3:c 3=(-20/9)*c 4+(-10/3)*c 5:=by
    linear_combination (-1120)*h1+(8400)*h2+(-16800)*h3+(9800)*h4
  have hn:a-1≠0:=sub_ne_zero.mpr neq
  let A0:K:=2*(108*a^3-190*a^2+100*a-15)
  let B0:K:=3*(63*a^4+54*a^3-235*a^2+148*a-24)
  have row0:A0*c 4+B0*c 5=0:=by
    have e:=two (0:Fin 3)
    norm_num [moment,Fin.sum_univ_succ] at e
    rw [c0,c1,c2,c3] at e
    apply (mul_eq_zero.mp (show (a^2*(a-1)^2)*(A0*c 4+B0*c 5)=0 from ?_)).resolve_left (mul_ne_zero (pow_ne_zero _ ha) (pow_ne_zero _ hn))
    dsimp only [A0,B0]
    linear_combination 1512*e
  let A1:K:=(7*a-4)*(27*a^2-30*a+5)
  let B1:K:=3*(56*a^4+49*a^3-198*a^2+115*a-16)
  have row1:A1*c 4+B1*c 5=0:=by
    have e:=two (1:Fin 3)
    norm_num [moment,Fin.sum_univ_succ] at e
    rw [c0,c1,c2,c3] at e
    apply (mul_eq_zero.mp (show (a^3*(a-1)^2)*(A1*c 4+B1*c 5)=0 from ?_)).resolve_left (mul_ne_zero (pow_ne_zero _ ha) (pow_ne_zero _ hn))
    dsimp only [A1,B1]
    linear_combination 1512*e
  let A2:K:=5*(56*a^3-91*a^2+42*a-5)
  let B2:K:=2*(126*a^4+112*a^3-427*a^2+234*a-30)
  have row2:A2*c 4+B2*c 5=0:=by
    have e:=two (2:Fin 3)
    norm_num [moment,Fin.sum_univ_succ] at e
    rw [c0,c1,c2,c3] at e
    apply (mul_eq_zero.mp (show (a^4*(a-1)^2)*(A2*c 4+B2*c 5)=0 from ?_)).resolve_left (mul_ne_zero (pow_ne_zero _ ha) (pow_ne_zero _ hn))
    dsimp only [A2,B2]
    linear_combination 2520*e
  let E:K:=189*a^4-490*a^3+465*a^2-192*a+30
  let F:K:=1512*a^4-3717*a^3+3290*a^2-1245*a+180
  have first:A0*B1-A1*B0=3*a*(a-1)^2*E:=by dsimp [A0,B0,A1,B1,E];ring
  have second:A0*B2-A2*B0=a*(a-1)^2*F:=by dsimp [A0,B0,A2,B2,F];ring
  have pair(i:K) (e:(A0*B1-A1*B0)*i=0) (f:(A0*B2-A2*B0)*i=0) : i=0:=by
    rw [first,mul_assoc (3*a*(a-1)^2)] at e
    rw [second,mul_assoc (a*(a-1)^2)] at f
    have ez:=(mul_eq_zero.mp e).resolve_left (mul_ne_zero (mul_ne_zero (by norm_num) ha) (pow_ne_zero _ hn))
    have fz:=(mul_eq_zero.mp f).resolve_left (mul_ne_zero ha (pow_ne_zero _ hn))
    dsimp only [E,F] at ez fz
    apply (mul_eq_zero.mp (show 87510*i=0 from ?_)).resolve_left (by norm_num)
    linear_combination (173677392*a^3-285630282*a^2+143132710*a-25063595)*ez+(-21709674*a^3+38618510*a^2-21693835*a+4177752)*fz
  have z4:c 4=0:=pair _ (by linear_combination B1*row0-B0*row1) (by linear_combination B2*row0-B0*row2)
  have z5:c 5=0:=pair _ (by linear_combination A0*row1-A1*row0) (by linear_combination A0*row2-A2*row0)
  funext i
  fin_cases i
  · change c 0=0
    simpa only [z4,z5,mul_zero,add_zero] using c0
  · change c 1=0
    simpa only [z4,z5,mul_zero,add_zero] using c1
  · change c 2=0
    simpa only [z4,z5,mul_zero,add_zero] using c2
  · change c 3=0
    simpa only [z4,z5,mul_zero,add_zero] using c3
  · exact z4
  · exact z5
end RKCert.Endpoint
namespace RKCert.EndpointPhysical
open RKCert.Endpoint Polynomial
variable {K:Type*} [Field K] [CharZero K]
/-- Genuine physical (unnormalized) clocks. -/
theorem physical_four_three (c:Fin 6→K) {u v:K} (hu:u≠0) (hv:v≠0) (different:v≠u)
    (one:∀k:Fin 4,moment c u (k.val+1)=0)
    (two:∀k:Fin 3,moment c v (k.val+2)-u*moment c v (k.val+1)=0) : c=0:=by
  have both:tests c u v 4:=⟨one,two 0,two 1⟩
  have sc:=normalize hu both
  apply (rescale_eq_zero_iff c hu).mp
  apply normalized_four_three _ _ (div_ne_zero hv hu) (fun e=>different ((div_eq_one_iff_eq hu).mp e)) sc.1
  intro k
  let a:=v/u
  have vu:u*a=v:=by dsimp [a];field_simp
  have mk(j:ℕ):moment c v j=u^(j+1)*moment (rescale c u) a j:=by simpa only [vu] using moment_rescale c u a j
  have raw:=two k
  rw [mk,mk] at raw
  have z:u^(k.val+3)*(moment (rescale c u) a (k.val+2)-moment (rescale c u) a (k.val+1))=0 :=by
    rw [show k.val+2+1=k.val+3 by omega,show k.val+1+1=k.val+2 by omega] at raw
    linear_combination raw
  exact (mul_eq_zero.mp z).resolve_left (pow_ne_zero _ hu)

/-- The reusable formal-primitive 4+3 obstruction on every original
degree-at-most-five polynomial. No monicity or real embedding. -/
theorem quintic_four_three (P:K[X]) (dp:P.natDegree≤5) {u v:K}
    (hu:u≠0) (hv:v≠0) (different:v≠u)
    (first:∀k:Fin 4,(Paired.primitive (X^(k.val+1)*P)).eval u=0)
    (next:∀k:Fin 3,(Paired.primitive (X^(k.val+1)*((X-C u)*P))).eval v=0) : P=0:=by
  let c:Fin 6→K:=fun i=>P.coeff i.val
  have eqn (t:K) (k:ℕ):(Paired.primitive (X^k*P)).eval t=moment c t k:=by
    rw [←formalPrimitive_eq_treePrimitive,Paired.primitive_eval_power_mul P t k dp]
    apply Finset.sum_congr rfl
    intro i _
    simp only [c,Nat.add_comm k i.val]
  have one(k:Fin 4):moment c u (k.val+1)=0:=(eqn u _).symm.trans (first k)
  have two(k:Fin 3):moment c v (k.val+2)-u*moment c v (k.val+1)=0:=by
    have z:=next k
    have s:X^(k.val+1)*((X-C u)*P)=X^(k.val+2)*P-u • (X^(k.val+1)*P):=by
      rw [show k.val+2=(k.val+1)+1 by omega,pow_succ,Polynomial.smul_eq_C_mul];ring
    rw [s,map_sub,map_smul,eval_sub,eval_smul,smul_eq_mul,eqn,eqn] at z
    exact z
  have cc:=physical_four_three c hu hv different one two
  ext j
  by_cases small:j<6
  · have h:=congrFun cc (⟨j,small⟩:Fin 6)
    simpa [c] using h
  · rw [coeff_zero,coeff_eq_zero_of_natDegree_lt (by omega: P.natDegree<j)]
end RKCert.EndpointPhysical

