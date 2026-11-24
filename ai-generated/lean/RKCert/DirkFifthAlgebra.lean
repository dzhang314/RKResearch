module
public import RKCert.DirkFifthMinor
public import RKCert.DirkQuintic43
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
@[expose] public section
namespace RKCert.PaidFifth
open Polynomial RKCert.Paired RKCert.Endpoint RKCert.EndpointPhysical
open scoped Matrix
variable {K:Type*} [Field K] [CharZero K]
noncomputable section
set_option maxHeartbeats 4000000

def matrix (t z:K) :Matrix (Fin 3) (Fin 3) K:=!![4*(5*t-2)*(7*t-6), 10*(12*t^3+10*t^2-28*t+9), 5*(21*t^4+18*t^3+15*t^2-68*t+24);
  12*(30*t^2-35*t+8), 45*(7*t^3+6*t^2-15*t+4), 5*(56*t^4+49*t^3+42*t^2-165*t+48);
  210*z^3-360*z^2+180*z-24, 210*z^4-450*z^2+300*z-45, 210*z^5-500*z^2+375*z-60]

omit [CharZero K] in
theorem det_matrix (t z:K):(matrix t z).det=150*t*(t-1)^2*minor 1 t z:=by
  simp [Matrix.det_fin_three,matrix,minor]
  ring

theorem unit_ports (c:Fin 6→K) (t z:K) (tn:t≠0) (td:t≠1) (hh:twoTests c t 3)
    (root:∑i:Fin 6,c i*z^i.val=0) (test:minor 1 t z≠0):c=0:=by
  have td':t-1≠0:=sub_ne_zero.mpr td
  have h1:c 0/2+c 1/3+c 2/4+c 3/5+c 4/6+c 5/7=0:=by
    have h:=hh.1 (0:Fin 3)
    norm_num [moment,Fin.sum_univ_succ] at h
    convert h using 1;ring
  have h2:c 0/3+c 1/4+c 2/5+c 3/6+c 4/7+c 5/8=0:=by
    have h:=hh.1 (1:Fin 3)
    norm_num [moment,Fin.sum_univ_succ] at h
    convert h using 1;ring
  have h3:c 0/4+c 1/5+c 2/6+c 3/7+c 4/8+c 5/9=0:=by
    have h:=hh.1 (2:Fin 3)
    norm_num [moment,Fin.sum_univ_succ] at h
    convert h using 1;ring
  have c0:c 0=(-4/35)*c 3+(-3/14)*c 4+(-2/7)*c 5:=by linear_combination 72*h1-240*h2+180*h3
  have c1:c 1=(6/7)*c 3+(10/7)*c 4+(25/14)*c 5:=by linear_combination -240*h1+900*h2-720*h3
  have c2:c 2=(-12/7)*c 3+(-15/7)*c 4+(-50/21)*c 5:=by linear_combination 180*h1-720*h2+600*h3
  have r0: (4*(5*t-2)*(7*t-6))*c 3+(10*(12*t^3+10*t^2-28*t+9))*c 4+(5*(21*t^4+18*t^3+15*t^2-68*t+24))*c 5=0:=by
    apply (mul_eq_zero.mp (show (t^2*(t-1)^2)*((4*(5*t-2)*(7*t-6))*c 3+(10*(12*t^3+10*t^2-28*t+9))*c 4+(5*(21*t^4+18*t^3+15*t^2-68*t+24))*c 5)=0 from ?_)).resolve_left
      (mul_ne_zero (pow_ne_zero _ tn) (pow_ne_zero _ td'))
    have h:=hh.2.1
    norm_num [moment,Fin.sum_univ_succ] at h
    rw [c0,c1,c2] at h
    linear_combination 840*h
  have r1: (12*(30*t^2-35*t+8))*c 3+(45*(7*t^3+6*t^2-15*t+4))*c 4+(5*(56*t^4+49*t^3+42*t^2-165*t+48))*c 5=0:=by
    apply (mul_eq_zero.mp (show (t^3*(t-1)^2)*((12*(30*t^2-35*t+8))*c 3+(45*(7*t^3+6*t^2-15*t+4))*c 4+(5*(56*t^4+49*t^3+42*t^2-165*t+48))*c 5)=0 from ?_)).resolve_left
      (mul_ne_zero (pow_ne_zero _ tn) (pow_ne_zero _ td'))
    have h:=hh.2.2
    norm_num [moment,Fin.sum_univ_succ] at h
    rw [c0,c1,c2] at h
    linear_combination 2520*h
  have r2:(210*z^3-360*z^2+180*z-24)*c 3+(210*z^4-450*z^2+300*z-45)*c 4+(210*z^5-500*z^2+375*z-60)*c 5=0:=by
    have h:=root
    norm_num [Fin.sum_univ_succ] at h
    rw [c0,c1,c2] at h
    linear_combination 210*h
  let x:Fin 3→K:=![c 3,c 4,c 5]
  have sys:(matrix t z).mulVec x=0:=by
    ext i
    fin_cases i
    · simpa [matrix,x,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,add_assoc] using r0
    · simpa [matrix,x,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,add_assoc] using r1
    · simpa [matrix,x,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,add_assoc] using r2
  have det:(matrix t z).det≠0:=by
    rw [det_matrix];exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) tn) (pow_ne_zero _ td')) test
  have zero:=Matrix.eq_zero_of_mulVec_eq_zero det sys
  have c3:c 3=0:=congrFun zero (0:Fin 3)
  have c4:c 4=0:=congrFun zero (1:Fin 3)
  have c5:c 5=0:=congrFun zero (2:Fin 3)
  ext i
  fin_cases i <;> first | exact c3 | exact c4 | exact c5 | simpa [c3,c4,c5] using c0 | simpa [c3,c4,c5] using c1 | simpa [c3,c4,c5] using c2

/-- The determinant callback applies to the actual quintic and its native
primitives, not normalized coefficients or surrogate node variables. -/
theorem quintic_ports {u v z:K} (un:u≠0) (vn:v≠0) (distinct:v≠u)
    (test:minor u v z≠0) (P:K[X]) (degree:P.natDegree≤5) (root:P.eval z=0)
    (first:∀k:Fin 3,(Paired.primitive (X^(k.val+1)*P)).eval u=0)
    (next:∀k:Fin 2,(Paired.primitive (X^(k.val+1)*((X-C u)*P))).eval v=0):P=0:=by
  let c:Fin 6→K:=fun i=>P.coeff i.val
  have eqn(t:K)(k:ℕ):(Paired.primitive (X^k*P)).eval t=moment c t k:=by
    rw [←formalPrimitive_eq_treePrimitive,Paired.primitive_eval_power_mul P t k degree]
    apply Finset.sum_congr rfl
    intro i _;simp only [c,Nat.add_comm k i.val]
  have two(k:Fin 2):moment c v (k.val+2)-u*moment c v (k.val+1)=0:=by
    have h:=next k
    have exp:X^(k.val+1)*((X-C u)*P)=X^(k.val+2)*P-u • (X^(k.val+1)*P):=by
      rw [show k.val+2=(k.val+1)+1 by omega,pow_succ,Polynomial.smul_eq_C_mul];ring
    rw [exp,map_sub,map_smul,eval_sub,eval_smul,smul_eq_mul,eqn,eqn] at h;exact h
  have cc:=normalize (c:=c) un (d:=3) (v:=v) ⟨fun k=>(eqn u _).symm.trans (first k),two 0,two 1⟩
  have uv:u*(v/u)=v:=by field_simp
  have uz:u*(z/u)=z:=by field_simp
  have sn:minor 1 (v/u) (z/u)≠0:=by
    intro h
    have e:=homogeneous u 1 (v/u) (z/u)
    rw [mul_one,uv,uz,h,mul_zero] at e;exact test e
  have ro:∑i:Fin 6,rescale c u i*(z/u)^i.val=0:=by
    calc
      _=∑i:Fin 6,c i*z^i.val:=by
        apply Finset.sum_congr rfl;intro i _;simp [rescale,mul_assoc,←mul_pow,uz]
      _=P.eval z:=by rw [eval_eq_sum_range' (n:=6) (by omega),←Fin.sum_univ_eq_sum_range]
      _=0:=root
  have cz:=(rescale_eq_zero_iff c un).mp (unit_ports _ _ _ (div_ne_zero vn un)
    (fun e=>distinct ((div_eq_one_iff_eq un).mp e)) cc ro sn)
  ext i
  by_cases small:i<6
  · simpa [c] using congrFun cz (⟨i,small⟩:Fin 6)
  · rw [coeff_zero,coeff_eq_zero_of_natDegree_lt (show P.natDegree < i by omega)]
end
end RKCert.PaidFifth

