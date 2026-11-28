module

public import RKCert.ReviewedNative.DIRK12MidpointLegendreProbeCore
public import RKCert.ReviewedNative.DIRK12MidpointRealForwardWiring
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! Actual paid scalar target profiles for the late three-clock probe.
Only verified quadrature through degree eleven is used. -/
namespace RKResearch.Certified.DIRK12MidpointShape

open RKResearch Graded Polynomial
open DIRK12MidpointRealInterval DIRK12MidpointForward DirectedRatBox
open scoped BigOperators Matrix Polynomial

def leg (d : Fin 3) (t : ℝ) : ℝ :=
  if d=0 then leg5 t else if d=1 then leg6 t else leg7 t

noncomputable def shape (d : Fin 3) : ℝ[X] :=
  ∑ i : Fin 8, Polynomial.C ((coef d i : Int):ℝ)*X^i.val

theorem shape_degree (d : Fin 3) : (shape d).natDegree≤d.val+5 := by
  unfold shape
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  by_cases low : i.val≤d.val+5
  · exact (natDegree_C_mul_X_pow_le _ _).trans low
  · rw [coef_bound d i (by omega),Int.cast_zero,map_zero,zero_mul,natDegree_zero]
    omega

theorem shape_eval (d : Fin 3) (t : ℝ) :
    (shape d).eval (1-t)=t*leg d t := by
  fin_cases d <;> norm_num [shape,coef,leg,leg5,leg6,leg7,Fin.sum_univ_succ,
    eval_finsetSum,eval_mul,eval_C,eval_pow,eval_X] <;> ring

theorem integral_shape (d : Fin 3) (k : Fin 7) (hk : k.val<d.val+5) :
    integral ((X:ℝ[X])^k.val*shape d)=if k=0 then 1 else 0 := by
  unfold shape
  rw [Finset.mul_sum,map_sum]
  have e (i : Fin 8) :
      integral ((X:ℝ[X])^k.val*(Polynomial.C ((coef d i : Int):ℝ)*X^i.val)) =
        ((coef d i : Int):ℝ)/((k.val+i.val+1 : Nat):ℝ) := by
    have eq : (X:ℝ[X])^k.val*(Polynomial.C ((coef d i : Int):ℝ)*X^i.val) =
        ((coef d i : Int):ℝ) • ((X:ℝ[X])^(k.val+i.val)) := by
      rw [Polynomial.smul_eq_C_mul,pow_add]
      ring
    rw [eq,map_smul,smul_eq_mul,integral_pow]
    push_cast
    ring
  simp_rw [e]
  have h := congrArg (fun r : Rat => (r:ℝ)) (reflected_integrals d k hk)
  by_cases z : k=0 <;>
    (simp [add8,add_assoc,Fin.sum_univ_succ,z,Rat.cast_div] at h ⊢
     norm_num at h ⊢
     exact h)

theorem paid_shape_degree (d : Fin 3) (k : Nat) (h : k+d.val+5<12) :
    (((X:ℝ[X])^k)*shape d).natDegree<12 := by
  refine Polynomial.natDegree_mul_le.trans_lt ?_
  rw [natDegree_pow, natDegree_X,mul_one]
  have hd := shape_degree d
  omega

noncomputable def actualProfile {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (d : Fin 3) :
    ι → ℝ := fun i => (nodes A) i*leg d ((nodes A) i)

theorem profile_probe {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (b : ι → ℝ)
    (quad : ∀ p : ℝ[X], p.natDegree<12 → DIRK12MidpointStar.quadr A b p=integral p)
    (d : Fin 3) (k : Fin 7) (hk : k.val<d.val+5) (paid : k.val+d.val+5<12) :
    row (DualSupport12.moment A b k.val) (actualProfile A d)=if k=0 then 1 else 0 := by
  have e := quad (X^k.val*shape d) (paid_shape_degree d k.val paid)
  rw [integral_shape d k hk,DIRK12MidpointStar.quadr_apply] at e
  simp only [eval_mul,eval_pow,eval_X,shape_eval] at e
  rw [row_apply,dotProduct,DualSupport12.moment]
  simp only [Pi.mul_apply,Pi.pow_apply,DualSupport12.reflected,Pi.sub_apply,Pi.one_apply,actualProfile]
  simpa only [mul_assoc] using e

theorem real_probe_target {x f : ℝ} (hx : Encloses xBox x) (hf : Encloses fBox f)
    (hx0 : realX x=0) (hf0 : realF x f=0)
    (A : Matrix (Fin 15) (Fin 15) ℝ)
    (clocks : ∀ i, ¬ghostRow i → 1-nodes A i=site x f (stageTag i))
    (d : Fin 3) (k : Fin 7) (hk : k.val<d.val+5) (paid : k.val+d.val+5<12) :
    row (DualSupport12.moment A (physicalWeight x f) k.val) (actualProfile A d)=
      if k=0 then 1 else 0 :=
  profile_probe A (physicalWeight x f)
    (scalar_and_star_with_physical_weights hx hf hx0 hf0 A clocks).1 d k hk paid

theorem probe_combo_positive {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (b : ι → ℝ)
    (quad : ∀ p : ℝ[X], p.natDegree<12 → DIRK12MidpointStar.quadr A b p=integral p)
    (coefs : Fin 3 → ℝ) (j : Fin 4) :
    row (DualSupport12.moment A b (j.val+1))
      (∑ d : Fin 3, coefs d • actualProfile A d)=0 := by
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro d _
  let k : Fin 7 := ⟨j.val+1,by omega⟩
  have low : k.val<d.val+5 := by dsimp [k]; omega
  have paid : k.val+d.val+5<12 := by dsimp [k]; omega
  have h := profile_probe A b quad d k low paid
  have hk : k≠0 := by
    intro e
    have v := congrArg Fin.val e
    change j.val+1=0 at v
    omega
  rw [ite_eq_right hk] at h
  change row (DualSupport12.moment A b (j.val+1)) (actualProfile A d)=0 at h
  rw [map_smul,smul_eq_mul,h,mul_zero]

end RKResearch.Certified.DIRK12MidpointShape

#print axioms RKResearch.Certified.DIRK12MidpointShape.integral_shape
#print axioms RKResearch.Certified.DIRK12MidpointShape.real_probe_target
#print axioms RKResearch.Certified.DIRK12MidpointShape.probe_combo_positive
