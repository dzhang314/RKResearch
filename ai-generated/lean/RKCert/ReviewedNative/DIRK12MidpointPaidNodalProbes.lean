module

public import RKCert.ReviewedNative.DIRK12MidpointPolynomialPrimitive
public import RKCert.ReviewedNative.DIRK12MidpointLegendreProbes
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! The exact scalar candidate for the degree-six nodal forward
input pays the same three actual late probes as the lower profiles.
This is not an assertion that the still-unproved reverse rows realize it. -/
namespace RKResearch.Certified.DIRK12MidpointProbes

open RKResearch Graded Polynomial
open DIRK12MidpointRealInterval DirectedRatBox
open scoped Polynomial Matrix BigOperators

noncomputable def openingNodal (x f : ℝ) : ℝ[X] := hull (fixed x f).tail

theorem openingNodal_degree (x f : ℝ) : (openingNodal x f).natDegree=6 := by
  rw [openingNodal,hull_degree]
  rfl

theorem openingNodal_factor (x f : ℝ) :
    (X:ℝ[X])*openingNodal x f=hull (fixed x f) := by
  unfold openingNodal fixed
  simp [hull]

def momentGap (n : Fin 6 → ℝ) : ℝ := lab n-lbb n
noncomputable def fitScale (n : Fin 6 → ℝ) : ℝ := cc n/(6*momentGap n)

theorem momentGap_pos {x f : ℝ} (hx : Encloses xBox x) (hf : Encloses fBox f) :
    0<momentGap (moments x f) := by
  have h := moments_enclosed hx hf
  have eq : momentGap (moments x f) = lab (moments x f)-(moments x f 1)^2 := by
    unfold momentGap lbb
    ring
  rw [eq]
  exact positive (enclose_sub (pAB h) (enclose_pow (h 1) 2)) (by decide +kernel)

theorem top_paid_relation {x f : ℝ} (hx0 : realX x=0) (hf0 : realF x f=0) (k : Fin 3) :
    let n := moments x f
    ((k.val+2:Nat):ℝ)*
      (ee n*n ⟨k.val,by omega⟩-cc n*n ⟨k.val+1,by omega⟩) -
      6*momentGap n*n ⟨k.val+1,by omega⟩=0 := by
  let n := moments x f
  have rel := (DIRK12Q36Moments.real_relations hx0 hf0).1
  fin_cases k
  · simpa [n,ee,cc,lab,lbb,momentGap,DIRK12MidpointMomentTransfers.C,pow_two] using
      (DIRK12MidpointMomentTransfers.paid_pair0 (n 0) (n 1) (n 2))
  · simpa [n,ee,cc,lab,lbb,momentGap,DIRK12MidpointMomentTransfers.C,pow_two] using
      (DIRK12MidpointMomentTransfers.paid_pair1 (n 0) (n 1) (n 2))
  · have r := DIRK12MidpointMomentTransfers.paid_pair2 (n 0) (n 1) (n 2) (n 3)
    rw [show DIRK12MidpointMomentTransfers.rel3 (n 0) (n 1) (n 2) (n 3)=0 from rel,mul_zero] at r
    simpa [n,ee,cc,lab,lbb,momentGap,DIRK12MidpointMomentTransfers.C,pow_two] using r

theorem fit_scale_relation {x f : ℝ} (hx : Encloses xBox x) (hf : Encloses fBox f)
    (hx0 : realX x=0) (hf0 : realF x f=0) (k : Fin 3) :
    let n := moments x f
    fitScale n*(U n*n ⟨k.val,by omega⟩-n ⟨k.val+1,by omega⟩) =
      n ⟨k.val+1,by omega⟩/((k.val+2:Nat):ℝ) := by
  let n := moments x f
  let a := n ⟨k.val,by omega⟩
  let b := n ⟨k.val+1,by omega⟩
  let j : ℝ := ((k.val+2:Nat):ℝ)
  change fitScale n*(U n*a-b)=b/j
  have d : 6*momentGap n≠0 := mul_ne_zero (by norm_num) (momentGap_pos hx hf).ne'
  have c : cc n≠0 := (all_pivots (moments_enclosed hx hf)).2.2.1.ne'
  have j0 : j≠0 := Nat.cast_ne_zero.mpr (by omega)
  have h := top_paid_relation hx0 hf0 k
  change j*(ee n*a-cc n*b)-6*momentGap n*b=0 at h
  calc
    _ = (ee n*a-cc n*b)/(6*momentGap n) := by
      unfold fitScale U
      field_simp [c,d]
    _ = _ := by
      apply (div_eq_div_iff d j0).2
      linear_combination h

/-- In reflected coordinates this is
\(\Lambda (u-Y)Q^\#(Y)-\int_Y^1 Q^\#(s)\,ds\). -/
noncomputable def nodalTarget (x f : ℝ) : ℝ[X] :=
  fitScale (moments x f) •
    ((Polynomial.C (U (moments x f))-X)*openingNodal x f) -
       fromOne (openingNodal x f)

theorem nodalTarget_degree (x f : ℝ) : (nodalTarget x f).natDegree≤7 := by
  unfold nodalTarget
  refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · refine (Polynomial.natDegree_smul_le _ _).trans ?_
    refine Polynomial.natDegree_mul_le.trans ?_
    rw [openingNodal_degree]
    have q := Polynomial.natDegree_sub_le (Polynomial.C (U (moments x f))) (X:ℝ[X])
    simp only [Polynomial.natDegree_C,Polynomial.natDegree_X,zero_max] at q
    omega
  · exact (fromOne_degree (openingNodal x f)).trans (by rw [openingNodal_degree])

theorem integral_nodal_target {x f : ℝ} (hx : Encloses xBox x) (hf : Encloses fBox f)
    (hx0 : realX x=0) (hf0 : realF x f=0) (k : Fin 3) :
    integral ((X:ℝ[X])^(k.val+1)*nodalTarget x f)=0 := by
  let n := moments x f
  let P := openingNodal x f
  let H := hull (fixed x f)
  have eqH : (X:ℝ[X])*P=H := openingNodal_factor x f
  have e : (X:ℝ[X])^(k.val+1)*((Polynomial.C (U n)-X)*P) =
      U n • ((X:ℝ[X])^k.val*H)-(X:ℝ[X])^(k.val+1)*H := by
    rw [←eqH,Polynomial.smul_eq_C_mul,pow_succ]
    ring
  have ep : (X:ℝ[X])^(k.val+1+1)*P=(X:ℝ[X])^(k.val+1)*H := by
    rw [pow_succ, mul_assoc,eqH]
  have first : integral (((X:ℝ[X])^(k.val+1))*((Polynomial.C (U n)-X)*P)) =
      U n*n ⟨k.val,by omega⟩-n ⟨k.val+1,by omega⟩ := by
    rw [e,map_sub,map_smul,smul_eq_mul]
    change U n*integral ((X:ℝ[X])^k.val*hull (fixed x f))-
      integral ((X:ℝ[X])^(k.val+1)*hull (fixed x f))=_
    rw [integral_hull,integral_hull]
    rfl
  have second : integral ((X:ℝ[X])^(k.val+1)*fromOne P)=
      n ⟨k.val+1,by omega⟩/((k.val+2:Nat):ℝ) := by
    rw [fromOne_paid,ep]
    change integral ((X:ℝ[X])^(k.val+1)*hull (fixed x f)) / ((k.val+2:Nat):ℝ)=_
    rw [integral_hull]
    rfl
  have expand : (X:ℝ[X])^(k.val+1)*nodalTarget x f =
      fitScale n • ((X:ℝ[X])^(k.val+1)*((Polynomial.C (U n)-X)*P)) -
      (X:ℝ[X])^(k.val+1)*fromOne P := by
    unfold nodalTarget
    simp only [Polynomial.smul_eq_C_mul]
    ring
  rw [expand,map_sub,map_smul,smul_eq_mul,first,second]
  exact sub_eq_zero.mpr (fit_scale_relation hx hf hx0 hf0 k)

theorem actual_nodal_probe {x f : ℝ} (hx : Encloses xBox x) (hf : Encloses fBox f)
    (hx0 : realX x=0) (hf0 : realF x f=0)
    (A : Matrix (Fin 15) (Fin 15) ℝ)
    (clocks : ∀ i, ¬ghostRow i → 1-nodes A i=site x f (stageTag i)) (k : Fin 3) :
    row (DualSupport12.moment A (physicalWeight x f) (k.val+1))
      (fun i => (nodalTarget x f).eval (1-nodes A i))=0 := by
  have deg : (((X:ℝ[X])^(k.val+1))*nodalTarget x f).natDegree<12 := by
    refine Polynomial.natDegree_mul_le.trans_lt ?_
    rw [natDegree_pow,natDegree_X,mul_one]
    have h := nodalTarget_degree x f
    omega
  have g := (scalar_and_star_with_physical_weights hx hf hx0 hf0 A clocks).1 _ deg
  rw [integral_nodal_target hx hf hx0 hf0 k,DIRK12MidpointStar.quadr_apply] at g
  simp only [eval_mul,eval_pow,eval_X] at g
  rw [row_apply,dotProduct,DualSupport12.moment]
  simp only [Pi.mul_apply,Pi.pow_apply,DualSupport12.reflected,Pi.sub_apply,Pi.one_apply]
  simpa only [mul_assoc] using g

end RKResearch.Certified.DIRK12MidpointProbes

#print axioms RKResearch.Certified.DIRK12MidpointProbes.fit_scale_relation
#print axioms RKResearch.Certified.DIRK12MidpointProbes.integral_nodal_target
#print axioms RKResearch.Certified.DIRK12MidpointProbes.actual_nodal_probe
