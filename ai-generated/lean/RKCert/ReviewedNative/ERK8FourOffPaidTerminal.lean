module

public import RKCert.ReviewedNative.ERK8FourOffNodalTransfer

import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! # The terminal hull can first be earned without a clean invertibility assumption -/
namespace RKResearch.Certified.Graded.FourOffNewton

open Polynomial RKResearch OneOff ERKTaggedHorizon FourOffPhysical ERK8CharEleven RKCert.Endpoint
open RKResearch.Certified.Graded.MultiOff.FourOff8CleanShape
open scoped Classical Matrix

variable {K : Type*} [Field K]
variable {A : Matrix (Fin 10) (Fin 10) K} {b : Fin 10→K} {P R : K[X]} {dup k : Fin 10}

theorem paid_terminal_hull_raw (M : Placement A b P dup k)
    {S : Finset K} (Sc : S.card=4)
    (T : CleanTerminalProfile A (nodalHull S) R) :
    ∃ sig : K, nodalHull S+P*R=C sig*nodalHull (offKnots A) := by
  let F := nodalHull S+P*R
  have sd : (nodalHull S).natDegree=4 := (natDegree_nodalHull _).trans Sc
  have fd : F.natDegree≤4 := natDegree_add_le_of_degree_le sd.le
    (natDegree_mul_le_of_le M.rankData.headDegree T.degR)
  have r (x : K) (hx : x∈offKnots A) : F.eval x=0 := by
    obtain ⟨j,gj,hj⟩ := mem_offKnots.mp hx
    have ne : j≠lastPhysical := fun e=>gj (e.symm ▸ M.rankData.cleanNine)
    have h := congrFun T.profile j
    simp only [Pi.add_apply,evalNodes_apply,diag_apply,Pi.smul_apply,Pi.single_eq_of_ne ne,
      smul_zero] at h
    rw [←hj]
    simpa only [F,eval_add,eval_mul,M.rankData.fit j gj] using h
  exact polynomial_hull_of_test_zeros (offKnots A) F (by
    rw [M.rankData.offCard]; exact fd) r

theorem eval_off_ne (M : Placement A b P dup k) (x : K) (hx : x∈offKnots A) :
    P.eval x≠0 := by
  obtain ⟨j,gj,rfl⟩ := mem_offKnots.mp hx
  rw [M.rankData.fit j gj]
  exact gj

theorem nodalHull_eval_ne_of_notMem {S : Finset K} {x : K} (hx : x∉S) :
    (nodalHull S).eval x≠0 := by
  simp only [nodalHull,eval_prod,eval_sub,eval_X,eval_C,Finset.prod_ne_zero_iff]
  intro y hy
  exact sub_ne_zero.mpr (fun e=>hx (e.symm ▸ hy))

/-- A fitted quadratic can share no clean root if it has at most one
candidate such root. This uses the literal terminal hull equality:
a zero terminal multiplier forces divisibility, and a nonzero
multiplier would turn the shared clean node into an actual off node. -/
theorem no_paid_single_shared_root (M : Placement A b P dup k)
    {S : Finset K} (Sc : S.card=4) (T : CleanTerminalProfile A (nodalHull S) R)
    (Pd : P.natDegree=2) {u : K} (hu : u∈S) (hit : P.eval u=0)
    (others : ∀ x∈S, x≠u → P.eval x≠0) : False := by
  obtain ⟨sig,F⟩ := paid_terminal_hull_raw M Sc T
  have dvd : ¬ P∣nodalHull S := by
    intro d
    have fac : nodalHull S=(X-C u)*nodalHull (S.erase u) := by
      unfold nodalHull
      exact (Finset.mul_prod_erase S (fun t : K=>(X:K[X])-C t) hu).symm
    have cp := coprime_nodalHull_of_eval_ne (S:=S.erase u) (P:=P)
      (fun x hx=>others _ (Finset.mem_of_mem_erase hx) (Finset.ne_of_mem_erase hx))
    rw [fac,mul_comm] at d
    have l := cp.dvd_of_dvd_mul_left d
    have N := natDegree_le_of_dvd l (X_sub_C_ne_zero u)
    rw [Pd,natDegree_X_sub_C] at N
    omega
  have sn : sig≠0 := by
    intro h
    apply dvd
    have z : nodalHull S+P*R=0 := by simpa [h] using F
    exact ⟨-R,by linear_combination z⟩
  have eq := congrArg (fun F : K[X]=>F.eval u) F
  simp only [eval_add,eval_mul,eval_C,hit,zero_mul,add_zero,nodalHull_eval_of_mem hu] at eq
  have huv := (mul_eq_zero.mp eq.symm).resolve_left sn
  have off : u∈offKnots A := by
    by_contra n
    exact nodalHull_eval_ne_of_notMem n huv
  exact eval_off_ne M _ off hit

end RKResearch.Certified.Graded.FourOffNewton

#print axioms RKResearch.Certified.Graded.FourOffNewton.no_paid_single_shared_root
