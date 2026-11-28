module

public import RKCert.ReviewedNative.DIRK12MidpointPaidNodalProbes
public import RKCert.ReviewedNative.DIRK12MidpointPolynomialVector
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! The fourth paid probe of the degree-seven nodal target. It uses
exactly degree eleven of true scalar quadrature. -/
namespace RKResearch.Certified.DIRK12MidpointProbes

open RKResearch Graded Polynomial
open DIRK12MidpointRealInterval DirectedRatBox
open scoped BigOperators Polynomial Matrix

theorem fit_scale_degree4 {x f : ℝ} (hx : Encloses xBox x) (hf : Encloses fBox f)
    (hx0 : realX x=0) (hf0 : realF x f=0) :
    let n := moments x f
    fitScale n*(U n*n 3-n 4)=n 4/5 := by
  let n := moments x f
  change fitScale n*(U n*n 3-n 4)=n 4/5
  have h4 := (DIRK12Q36Moments.real_relations hx0 hf0).2
  have h := DIRK12MidpointMomentTransfers.paid_pair3 (n 0) (n 1) (n 2) (n 3) (n 4)
  rw [show DIRK12MidpointMomentTransfers.rel4 (n 0) (n 1) (n 2) (n 3) (n 4)=0 from h4,
    neg_zero] at h
  change 5*((ee n)*n 3-
      DIRK12MidpointMomentTransfers.C ((n 0)*(n 2)) ((n 1)*(n 1))*n 4)-
      6*(n 0*n 2-n 1*n 1)*n 4=0 at h
  have e : 5*(ee n*n 3-cc n*n 4)-6*momentGap n*n 4=0 := by
    simp only [cc,lab,lbb,momentGap,DIRK12MidpointMomentTransfers.C] at h ⊢
    exact h
  have hg : 6*momentGap n≠0 := mul_ne_zero (by norm_num) (momentGap_pos hx hf).ne'
  have hc : cc n≠0 := (all_pivots (moments_enclosed hx hf)).2.2.1.ne'
  calc
    _ = (ee n*n 3-cc n*n 4)/(6*momentGap n) := by
      unfold fitScale U
      field_simp [hc,hg]
    _ = _ := by
      apply (div_eq_div_iff hg (by norm_num : (5:ℝ)≠0)).2
      linear_combination e

theorem integral_nodal_fourth {x f : ℝ} (hx : Encloses xBox x) (hf : Encloses fBox f)
    (hx0 : realX x=0) (hf0 : realF x f=0) :
    integral ((X:ℝ[X])^4*nodalTarget x f)=0 := by
  let n := moments x f
  let P := openingNodal x f
  let H := hull (fixed x f)
  have eqH : (X:ℝ[X])*P=H := openingNodal_factor x f
  have e : (X:ℝ[X])^4*((C (U n)-X)*P) =
      U n • ((X:ℝ[X])^3*H)-(X:ℝ[X])^4*H := by
    rw [←eqH,Polynomial.smul_eq_C_mul]
    ring
  have ep : (X:ℝ[X])^5*P=(X:ℝ[X])^4*H := by rw [←eqH]; ring
  have first : integral ((X:ℝ[X])^4*((C (U n)-X)*P))=U n*n 3-n 4 := by
    rw [e,map_sub,map_smul,smul_eq_mul]
    change U n*integral ((X:ℝ[X])^3*hull (fixed x f))-
      integral ((X:ℝ[X])^4*hull (fixed x f))=_
    rw [integral_hull,integral_hull]
    rfl
  have second : integral ((X:ℝ[X])^4*fromOne P)=n 4/5 := by
    rw [fromOne_paid,ep]
    change integral ((X:ℝ[X])^4*hull (fixed x f))/(5:ℝ)=_
    rw [integral_hull]
    rfl
  have expand : (X:ℝ[X])^4*nodalTarget x f =
      fitScale n • ((X:ℝ[X])^4*((C (U n)-X)*P))-(X:ℝ[X])^4*fromOne P := by
    unfold nodalTarget
    simp only [Polynomial.smul_eq_C_mul]
    ring
  rw [expand,map_sub,map_smul,smul_eq_mul,first,second]
  exact sub_eq_zero.mpr (fit_scale_degree4 hx hf hx0 hf0)

theorem row_power_quadrature {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (b : ι → ℝ)
    (quad : ∀ q : ℝ[X], q.natDegree < 12 → DIRK12MidpointStar.quadr A b q=integral q)
    (k : Nat) (p : ℝ[X]) (hd : k+p.natDegree < 12) :
    row (DualSupport12.moment A b k) (Vector.evalVector (1-nodes A) p)=
      integral ((X:ℝ[X])^k*p) := by
  have hp : (((X:ℝ[X])^k)*p).natDegree < 12 := by
    apply Polynomial.natDegree_mul_le.trans_lt
    simpa [natDegree_pow] using hd
  have h := quad _ hp
  rw [DIRK12MidpointStar.quadr_apply] at h
  simp only [eval_mul,eval_pow,eval_X] at h
  rw [row_apply,dotProduct,DualSupport12.moment]
  simp only [Pi.mul_apply,Pi.pow_apply,DualSupport12.reflected,Vector.at_apply,
    Pi.sub_apply,Pi.one_apply]
  simpa only [mul_assoc] using h

theorem scalar_fromOne_moment {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (b : ι → ℝ)
    (quad : ∀ q : ℝ[X], q.natDegree < 12 → DIRK12MidpointStar.quadr A b q=integral q)
    (k : Nat) (p : ℝ[X]) (hd : k+1+p.natDegree < 12) :
    row (DualSupport12.moment A b k) (Vector.evalVector (1-nodes A) (fromOne p))=
      row (DualSupport12.moment A b (k+1)) (Vector.evalVector (1-nodes A) p)/((k+1:Nat):ℝ) := by
  have a : k+(fromOne p).natDegree < 12 := by
    have h := fromOne_degree p
    omega
  rw [row_power_quadrature A b quad _ _ a,
    row_power_quadrature A b quad _ _ hd,fromOne_paid]

theorem actual_nodal_all_four {x f : ℝ}
    (hx : Encloses xBox x) (hf : Encloses fBox f) (hx0 : realX x=0) (hf0 : realF x f=0)
    (A : Matrix (Fin 15) (Fin 15) ℝ)
    (clocks : ∀ i, ¬ghostRow i → 1-nodes A i=site x f (stageTag i)) (k : Fin 4) :
    row (DualSupport12.moment A (physicalWeight x f) (k.val+1))
      (Vector.evalVector (1-nodes A) (nodalTarget x f))=0 := by
  have hd := nodalTarget_degree x f
  have t : k.val+1+(nodalTarget x f).natDegree < 12 := by omega
  by_cases e : k.val=3
  · rw [row_power_quadrature A _ (scalar_and_star_with_physical_weights hx hf hx0 hf0 A clocks).1 _ _ t,
      show k.val+1=4 by omega,integral_nodal_fourth hx hf hx0 hf0]
  · have ks := k.isLt
    exact actual_nodal_probe hx hf hx0 hf0 A clocks ⟨k.val,by omega⟩

end RKResearch.Certified.DIRK12MidpointProbes

#print axioms RKResearch.Certified.DIRK12MidpointProbes.fit_scale_degree4
#print axioms RKResearch.Certified.DIRK12MidpointProbes.integral_nodal_fourth
#print axioms RKResearch.Certified.DIRK12MidpointProbes.actual_nodal_all_four
