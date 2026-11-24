module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Splits

@[expose] public section

/-! # An affine lowering remainder bounds the number of repeated roots

If the derivative of an actual polynomial has a Bezout-type relation
with a coprime second polynomial and a nonzero affine remainder, the
whole pencil fiber can lose at most one distinct root. No modular
discriminant or positivity argument is used.
-/
namespace RKCert.FixedPolynomial
open Polynomial
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

private theorem eval_right_ne_of_coprime {F L : K[X]} (h : IsCoprime F L) {x : K}
    (f0 : F.eval x=0) : L.eval x≠0 := by
  obtain ⟨a,b,ab⟩ := h
  intro l0
  have eq := congrArg (eval x) ab
  simp only [eval_add,eval_mul,eval_one,f0,l0,mul_zero,add_zero] at eq
  exact zero_ne_one eq

private theorem affine_derivative_ne_at_root {V : K[X]} (vne : V≠0)
    (vd : V.natDegree≤1) {x : K} (z : V.eval x=0) : V.derivative.eval x≠0 := by
  have vp : 0<V.natDegree := by
    by_contra! h
    have e := eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero h)
    apply vne
    rw [e,eval_C] at z
    rw [e,z,map_zero]
  have d0 : V.derivative.natDegree=0 := by
    have e := natDegree_derivative_le V
    omega
  have e := eq_C_of_natDegree_eq_zero d0
  intro zd
  rw [e,eval_C] at zd
  exact (derivative_ne_zero.mpr (Nat.ne_of_gt vp)) (by rw [e,zd,map_zero])

set_option maxHeartbeats 1200000 in
theorem distinct_roots_of_affine_lowering {F L P U V : K[X]}
    (fn : F≠0) (split : F.Splits) (co : IsCoprime F L)
    (vn : V≠0) (vd : V.natDegree≤1) (diff : P*F.derivative=U*F+V*L) :
    F.natDegree≤F.roots.toFinset.card+1 := by
  have repeated (x : K) (m : 1<rootMultiplicity x F) :
      F.eval x=0 ∧ F.derivative.eval x=0 ∧ V.eval x=0 := by
    obtain ⟨f0,df0⟩ := (one_lt_rootMultiplicity_iff_isRoot fn).mp m
    have z := congrArg (eval x) diff
    simp only [eval_mul,eval_add,IsRoot.def] at f0 df0 z
    rw [f0,df0,mul_zero,mul_zero,zero_add] at z
    exact ⟨f0,df0,(mul_eq_zero.mp z.symm).resolve_right (eval_right_ne_of_coprime co f0)⟩
  have double (x : K) : rootMultiplicity x F≤2 := by
    by_contra! big
    obtain ⟨f0,df0,v0⟩ := repeated x (by omega)
    have third : (X-C x)^3∣F := (le_rootMultiplicity_iff fn).mp (by omega)
    have df2 := pow_sub_dvd_iterate_derivative_of_pow_dvd 2 third
    have d2 : X-C x∣F.derivative.derivative := by
      change (X-C x)^1∣(Polynomial.derivative^[2] F) at df2
      simpa only [pow_one,Function.iterate_succ_apply',Function.iterate_zero_apply] using df2
    have d0 : F.derivative.derivative.eval x=0 := dvd_iff_isRoot.mp d2
    have neA := affine_derivative_ne_at_root vn vd v0
    have neB := eval_right_ne_of_coprime co f0
    have e := congrArg (eval x) (congrArg Polynomial.derivative diff)
    simp only [derivative_mul,map_add,eval_mul,eval_add,f0,df0,v0,mul_zero,zero_mul,zero_add,
      add_zero] at e
    rw [d0,mul_zero] at e
    exact (mul_ne_zero neA neB) e.symm
  let S := F.roots.toFinset
  let Z := S.filter (fun x => V.eval x=0)
  have cap : Z.card≤1 := by
    have sub : Z⊆V.roots.toFinset := by
      intro x hx
      exact Multiset.mem_toFinset.mpr ((mem_roots vn).mpr (Finset.mem_filter.mp hx).2)
    exact (Finset.card_le_card sub).trans ((Multiset.toFinset_card_le V.roots).trans ((card_roots' V).trans vd))
  calc
    F.natDegree = ∑ x∈S,F.roots.count x :=
      split.natDegree_eq_card_roots.trans (Multiset.toFinset_sum_count_eq _).symm
    _ ≤ ∑ x∈S,(1 + if V.eval x=0 then 1 else 0) := by
      apply Finset.sum_le_sum
      intro x _
      rw [count_roots]
      by_cases h : V.eval x=0
      · simpa only [h,ite_true] using double x
      · simp only [h,ite_false,add_zero]
        by_contra! e
        exact h (repeated x e).2.2
    _ = S.card+Z.card := by simp [Finset.sum_add_distrib,Z]
    _ ≤ S.card+1 := Nat.add_le_add_left cap _

end
end RKCert.FixedPolynomial
