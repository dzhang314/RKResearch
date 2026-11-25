module

public import RKCert.ReviewedNative.ERKHeadContrast
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # A cubic cut from the literal first three and second two primitive tests

This scalar lemma has no fixed RK tableau or assumed sign of a stage clock.
The only normalization is the invertible dilation by the first nonzero
physical clock.
-/
namespace RKResearch.Certified.Graded.NativeCubicTwoPort

open Polynomial RKCert.ReviewedNative.TwoKnot
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

private theorem normalized (c : Fin 4→K) (t : K) (ht : t≠0) (h1 : t≠1)
    (first : ∀k : Fin 3, moment c 1 (k.val+1)=0)
    (second : ∀k : Fin 2, moment c t (k.val+2)-moment c t (k.val+1)=0) : c=0 := by
  have f₀ : c 0/2+c 1/3+c 2/4+c 3/5=0 := by
    have f := first (0 : Fin 3)
    norm_num [moment,Fin.sum_univ_succ] at f
    convert f using 1 <;> ring
  have f₁ : c 0/3+c 1/4+c 2/5+c 3/6=0 := by
    have f := first (1 : Fin 3)
    norm_num [moment,Fin.sum_univ_succ] at f
    convert f using 1 <;> ring
  have f₂ : c 0/4+c 1/5+c 2/6+c 3/7=0 := by
    have f := first (2 : Fin 3)
    norm_num [moment,Fin.sum_univ_succ] at f
    convert f using 1 <;> ring
  have c₀ : c 0=(-4/35:K)*c 3 := by
    linear_combination 72*f₀-240*f₁+180*f₂
  have c₁ : c 1=(6/7:K)*c 3 := by
    linear_combination -240*f₀+900*f₁-720*f₂
  have c₂ : c 2=(-12/7:K)*c 3 := by
    linear_combination 180*f₀-720*f₁+600*f₂
  have c₃ : c 3=0 := by
    by_contra nz
    have f := second (0 : Fin 2)
    have g := second (1 : Fin 2)
    norm_num [moment,Fin.sum_univ_succ] at f g
    rw [c₀,c₁,c₂] at f g
    have e : (t^2*(t-1)^2)*((5*t-2)*(7*t-6))*c 3=0 := by
      linear_combination (210:K)*f
    have z : (t^3*(t-1)^2)*(30*t^2-35*t+8)*c 3=0 := by
      linear_combination (210:K)*g
    have q := (mul_eq_zero.mp ((mul_eq_zero.mp e).resolve_right nz)).resolve_left
      (mul_ne_zero (pow_ne_zero _ ht) (pow_ne_zero _ (sub_ne_zero.mpr h1)))
    have r := (mul_eq_zero.mp ((mul_eq_zero.mp z).resolve_right nz)).resolve_left
      (mul_ne_zero (pow_ne_zero _ ht) (pow_ne_zero _ (sub_ne_zero.mpr h1)))
    rcases mul_eq_zero.mp q with d|d
    · have t₂ : t=(2:K)/5 := (eq_div_iff (by norm_num : (5:K)≠0)).mpr (by
        linear_combination d)
      rw [t₂] at r
      norm_num at r
    · have t₆ : t=(6:K)/7 := (eq_div_iff (by norm_num : (7:K)≠0)).mpr (by
        linear_combination d)
      rw [t₆] at r
      norm_num at r
  ext i
  fin_cases i
  · change c 0=0
    simpa only [c₃,mul_zero] using c₀
  · change c 1=0
    simpa only [c₃,mul_zero] using c₁
  · change c 2=0
    simpa only [c₃,mul_zero] using c₂
  · exact c₃

private def scaled (c : Fin 4→K) (a : K) : Fin 4→K := fun i=>c i*a^i.val

private theorem dilate (c : Fin 4→K) (a t : K) (k : ℕ) :
    moment c (a*t) k=a^(k+1)*moment (scaled c a) t k := by
  simp only [moment,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [scaled,mul_pow,pow_add,div_eq_mul_inv]
  ring

private theorem physical_coefficients (c : Fin 4→K) {a u : K}
    (ha : a≠0) (hu : u≠0) (different : u≠a)
    (first : ∀k : Fin 3, moment c a (k.val+1)=0)
    (second : ∀k : Fin 2, moment c u (k.val+2)-a*moment c u (k.val+1)=0) : c=0 := by
  let t := u/a
  have atU : a*t=u := by dsimp [t]; field_simp [ha] <;> ring
  have hs (k : Fin 3) : moment (scaled c a) 1 (k.val+1)=0 := by
    have h := dilate c a 1 (k.val+1)
    rw [mul_one,first k] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero _ ha)
  have ht (k : Fin 2) : moment (scaled c a) t (k.val+2)-moment (scaled c a) t (k.val+1)=0 := by
    have row (d : ℕ) : moment c u d=a^(d+1)*moment (scaled c a) t d := by
      simpa only [atU] using dilate c a t d
    have h := second k
    rw [row,row,show k.val+2+1=k.val+3 by omega,show k.val+1+1=k.val+2 by omega] at h
    have cancel : a^(k.val+3)*(moment (scaled c a) t (k.val+2)-
        moment (scaled c a) t (k.val+1))=0 := by
      rw [show a^(k.val+3)=a^(k.val+2)*a by simpa using (pow_succ a (k.val+2))] at h ⊢
      linear_combination h
    exact (mul_eq_zero.mp cancel).resolve_left (pow_ne_zero _ ha)
  have z := normalized (scaled c a) t (div_ne_zero hu ha)
    (fun e=>different ((div_eq_one_iff_eq ha).mp e)) hs ht
  ext i
  have e := congrFun z i
  change c i*a^i.val=0 at e
  exact (mul_eq_zero.mp e).resolve_right (pow_ne_zero _ ha)

/-- Two distinct, nonzero physical knots force the actual cubic profile
to vanish. The second test uses the polynomial mask X(X−a). -/
theorem eq_zero_of_primitive_ports {P : K[X]} (degree : P.natDegree≤3) {a u : K}
    (ha : a≠0) (hu : u≠0) (different : u≠a)
    (first : ∀k : Fin 3,(primitive (X^k.val*(X*P))).eval a=0)
    (second : ∀k : Fin 2,(primitive (X^k.val*((X*(X-C a))*P))).eval u=0) : P=0 := by
  let c : Fin 4→K := toFn 4 P
  have rep : ofFn 4 c=P := ofFn_comp_toFn_eq_id_of_natDegree_lt (by omega)
  have value (x : K) (k : ℕ) : (primitive (X^k*P)).eval x=moment c x k := by
    simpa only [rep] using HeadContrast.primitive_monomial_moment c x k
  have f (k : Fin 3) : moment c a (k.val+1)=0 := by
    have id : (X:K[X])^k.val*(X*P)=X^(k.val+1)*P := by rw [pow_succ,mul_assoc]
    simpa only [id,value] using first k
  have g (k : Fin 2) : moment c u (k.val+2)-a*moment c u (k.val+1)=0 := by
    have id : (X:K[X])^k.val*((X*(X-C a))*P)=X^(k.val+2)*P-a • (X^(k.val+1)*P) := by
      rw [show k.val+2=k.val+1+1 by omega]
      simp only [pow_succ,smul_eq_C_mul]
      ring
    simpa only [id,map_sub,map_smul,eval_sub,eval_smul,smul_eq_mul,value] using second k
  rw [←rep,physical_coefficients c ha hu different f g,ofFn_zero]

end
end RKResearch.Certified.Graded.NativeCubicTwoPort
